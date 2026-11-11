try:
    from ctypes import windll
    windll.shcore.SetProcessDpiAwareness(1)
except Exception:
    pass

from logging import root
from PIL import Image
import customtkinter as ctk
import cv2

import time, threading
import logging
from PIL import ImageOps
from datetime import datetime, timedelta
from collections import defaultdict
import sys, os
import tkinter as tk
import random
import math
import numpy as np
import json
import re
import glob
import base64
import shutil
import subprocess
import tempfile
from tkinter import filedialog, messagebox
import web_report


THAI_MONTHS = ("", "มกราคม", "กุมภาพันธ์", "มีนาคม", "เมษายน", "พฤษภาคม", "มิถุนายน",
               "กรกฎาคม", "สิงหาคม", "กันยายน", "ตุลาคม", "พฤศจิกายน", "ธันวาคม")
UI_LANGUAGE = "th"
BUILD = "v25 (2026-11-11)"  # shown in run.log only


def ui(thai, english):
    return english if UI_LANGUAGE == "en" else thai


# Prompt (Google Fonts, OFL) in four weights. Tk only knows "normal"/"bold", so
# Light and SemiBold are reached through their own family names, which both
# fontconfig (Pi) and Windows GDI register for the static TTF files.
# "Prompt TH" is Prompt with extra raised Thai tone marks (see
# tools/make_prompt_th.py and thai_marks below).
# Prompt-Medium is deliberately not bundled: Tk on Linux asks fontconfig for
# weight "medium" when it means normal, so with Medium installed every
# "Prompt" normal label would render in Medium instead of Regular.
FONT_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), "fonts")
PROMPT_WEIGHTS = {
    "light": ("Prompt TH Light", "normal", "PromptTH-Light.ttf"),       # small hints
    "regular": ("Prompt TH", "normal", "PromptTH-Regular.ttf"),         # body text
    "semibold": ("Prompt TH SemiBold", "normal", "PromptTH-SemiBold.ttf"),  # buttons, card titles
    "bold": ("Prompt TH", "bold", "PromptTH-Bold.ttf"),                 # page titles, big numbers
}
_PROMPT_READY = False


def ensure_prompt_files():
    """Restore fonts/PromptTH-*.ttf from EMBEDDED_FONTS if missing or damaged."""
    import hashlib
    import zlib
    for filename, (size, digest, chunks) in EMBEDDED_FONTS.items():
        path = os.path.join(FONT_DIR, filename)
        try:
            if os.path.getsize(path) == size:
                continue
        except OSError:
            pass
        data = zlib.decompress(base64.b64decode("".join(chunks)))
        if hashlib.sha256(data).hexdigest() != digest:
            logging.error("Embedded font %s is corrupt", filename)
            continue
        try:
            os.makedirs(FONT_DIR, exist_ok=True)
            with open(path + ".tmp", "wb") as output:
                output.write(data)
            os.replace(path + ".tmp", path)
            logging.info("Restored font %s", path)
        except OSError:
            logging.exception("Cannot write font %s", path)


def register_prompt_fonts():
    """Make the bundled Prompt files available to Tk before the first window."""
    ensure_prompt_files()
    loaded = 0
    for _, _, filename in PROMPT_WEIGHTS.values():
        path = os.path.join(FONT_DIR, filename)
        if not os.path.exists(path):
            logging.warning("Font file missing: %s", path)
            continue
        try:
            if ctk.FontManager.load_font(path):
                loaded += 1
        except Exception:
            logging.exception("Cannot load font %s", path)
    return loaded


# Larger text for older users. Every ui_font() size is multiplied by this.
# The fixed-size cards only have room for it on bigger screens, so it grows
# from 1.0 at 1024x600 to 1.45 at 1280x800 and above (checked at 1024x600,
# 1280x800 and 1536x864). FONT_SCALE=1.4 in the environment overrides it.
FONT_SCALE = 1.0


def set_font_scale(width, height):
    global FONT_SCALE
    forced = os.environ.get("FONT_SCALE")
    if forced:
        try:
            FONT_SCALE = max(.8, min(2.0, float(forced)))
            return
        except ValueError:
            logging.warning("Ignoring FONT_SCALE=%r", forced)
    room = min(width / 1280, height / 800)
    FONT_SCALE = max(1.0, min(1.45, 1.0 + (room - .75) * 1.8))


_TONE = "[\u0E48-\u0E4C]"
_TALL_CONSONANT = re.compile("([\u0E1B\u0E1D\u0E1F\u0E2C][\u0E38-\u0E3A]?)(" + _TONE + ")")
_SHORT_VOWEL = re.compile("([\u0E31\u0E34])(" + _TONE + ")")
_TALL_VOWEL = re.compile("([\u0E35-\u0E37\u0E47])(" + _TONE + ")")
_BEFORE_AM = re.compile("(" + _TONE + ")(?=\u0E33)")


def _private(base, mark):
    return chr(base + ord(mark) - 0x0E48)


def thai_marks(text):
    """Swap Thai tone marks for the pre-positioned copies in Prompt TH.

    Tk on Linux draws text without OpenType shaping, so a tone mark after an
    upper vowel lands on the vowel and vanishes (ที่ shows as ที, นิ้ว as นิว).
    Prompt TH carries raised and left-shifted copies of each tone mark at
    U+F710/F720/F730; this picks the right one for its context.
    """
    if not _PROMPT_READY or not isinstance(text, str) or "\u0E48" > max(text, default=" "):
        return text
    text = _TALL_CONSONANT.sub(lambda m: m.group(1) + _private(0xF730, m.group(2)), text)
    text = _SHORT_VOWEL.sub(lambda m: m.group(1) + _private(0xF710, m.group(2)), text)
    text = _TALL_VOWEL.sub(lambda m: m.group(1) + _private(0xF720, m.group(2)), text)
    return _BEFORE_AM.sub(lambda m: _private(0xF720, m.group(1)), text)


_TEXT_OPTIONS = ("text", "message", "detail")
_original_options = tk.Misc._options


def _options_with_thai_marks(self, cnf, kw=None):
    """Every widget option, canvas item and dialog passes through Misc._options."""
    def fix(options):
        if isinstance(options, dict) and any(k in options for k in _TEXT_OPTIONS):
            options = dict(options)
            for key in _TEXT_OPTIONS:
                if key in options:
                    options[key] = thai_marks(options[key])
        return options
    return _original_options(self, fix(cnf), fix(kw))


tk.Misc._options = _options_with_thai_marks


def ui_font(size, weight="regular", max_scale=None):
    """max_scale caps the enlargement for text in tight fixed-size spots."""
    size = max(1, round(size * (FONT_SCALE if max_scale is None else min(FONT_SCALE, max_scale))))
    family, tk_weight, _ = PROMPT_WEIGHTS[weight]
    if not _PROMPT_READY:  # Prompt not installed: keep the old Thai font
        family, tk_weight = "Sarabun", "normal" if weight in ("light", "regular") else "bold"
    return (family, size, tk_weight)


def hand_label(hand):
    return ui(hand, "Left" if hand == "ซ้าย" else "Right")


def pain_description(value):
    if value is None:
        return ui("ยังไม่ได้บอก", "Not recorded")
    if value == 0:
        return ui("ไม่ปวด", "No pain")
    if value <= 3:
        return ui("ปวดเล็กน้อย", "Mild pain")
    if value <= 6:
        return ui("ปวดปานกลาง", "Moderate pain")
    return ui("ปวดมาก", "Severe pain")


def pain_advice(before, after):
    """Short guidance from the 0-10 pain scores recorded on the home screen.

    Follows the usual pain-monitoring rule for hand exercise: mild pain (0-3)
    is acceptable, moderate pain means easing off, and severe or rising pain
    means stopping and seeing a professional. Not a diagnosis.
    """
    latest = after if after is not None else before
    if latest is None:
        return (ui("ยังไม่ได้บันทึก", "Not recorded"), "#52667A",
                ui("บันทึกระดับปวดที่หน้าหลัก ทั้งก่อนเริ่มและหลังฝึกเสร็จ",
                   "Record your pain on the home screen before and after practice."))
    if before is not None and after is not None:
        if after > before:
            change, color = ui("ปวดมากขึ้น", "More pain"), "#B83228"
        elif after < before:
            change, color = ui("ปวดลดลง", "Less pain"), "#137A4B"
        else:
            change, color = ui("ปวดเท่าเดิม", "No change"), "#52667A"
        headline = f"{before} → {after} · {change}"
    else:
        color = "#137A4B" if latest <= 3 else "#A56A00" if latest <= 6 else "#B83228"
        headline = ui(f"ก่อนฝึก {latest}/10", f"Before: {latest}/10")
    if latest >= 7:
        color = "#B83228"
        advice = ui("ปวดมาก ควรหยุดฝึกและพักมือ หากยังปวด บวม หรือนิ้วล็อกเหยียดไม่ออก ควรพบแพทย์หรือนักกายภาพบำบัด",
                    "Severe pain: stop and rest your hand. If pain, swelling or locking persists, see a doctor or physiotherapist.")
    elif before is not None and after is not None and after - before >= 2:
        advice = ui("ปวดเพิ่มขึ้นหลังฝึก ครั้งหน้าลดจำนวนรอบหรือเวลาค้างท่า และขยับเฉพาะช่วงที่ไม่เจ็บ",
                    "Pain rose after practice. Next time do fewer rounds or shorter holds, within a pain-free range.")
    elif latest >= 4:
        advice = ui("ปวดปานกลาง ฝึกเบาลงและพักให้มากขึ้น หากไม่ดีขึ้นใน 24 ชม. ควรปรึกษานักกายภาพบำบัด",
                    "Moderate pain: ease off and rest more. If it doesn't settle within 24 hours, consult a physiotherapist.")
    elif latest == 0:
        advice = ui("ไม่มีอาการปวด ฝึกตามโปรแกรมเดิมได้ต่อเนื่อง",
                    "No pain. Continue your usual programme.")
    else:
        advice = ui("ปวดเล็กน้อย อยู่ในระดับที่ฝึกต่อได้ ขยับช้า ๆ และไม่ฝืนเมื่อเจ็บ",
                    "Mild pain is acceptable. Keep moving slowly and don't push through sharp pain.")
    return headline, color, advice


def thai_datetime(value):
    return ui((f"วันที่ {value.day} {THAI_MONTHS[value.month]} พ.ศ. {value.year + 543} "
               f"เวลา {value.hour:02d}:{value.minute:02d} น."),
              value.strftime("%d %B %Y at %H:%M"))


def assess_completed_set(stable_poses):
    """Continuity feedback only; this is not a clinical assessment of the hand."""
    if stable_poses >= 12:
        return ui("ทำได้ต่อเนื่อง", "Steady practice"), "#1E8449", ui(
            "ทำท่าต่อเนื่องได้ดี พักมือก่อนเริ่มเซตถัดไป", "You practiced steadily. Rest before another set.")
    if stable_poses >= 8:
        return ui("มีช่วงพัก", "Some pauses"), "#9A6700", ui(
            "ทำครบแล้ว ครั้งหน้าลองขยับช้า ๆ และพักเมื่อเมื่อยมือ", "You finished. Move slowly and rest when tired.")
    return ui("หยุดพักหลายช่วง", "Several pauses"), "#C0392B", ui(
        "ทำครบแล้ว แต่มีช่วงที่ต้องหยุดบ่อย ลองจัดมือให้อยู่ในภาพและพักเมื่อเมื่อยมือ",
        "You finished with several pauses. Keep your hand in view and rest when tired.")


def improvement_tip(stable_poses):
    if stable_poses >= 12:
        return ui("ครั้งหน้า รักษาความต่อเนื่องแบบนี้ได้เลย", "Next time, keep this steady pace.")
    return ui((f"เซตหน้า ลองให้กล้องจับต่อเนื่องอีก {12 - stable_poses} ท่า "
               f"เพื่อให้ได้อย่างน้อย 12 จาก 15 ท่า"),
              f"Next time, try {12 - stable_poses} more poses with steady camera tracking.")


def choose_camera_device():
    explicit = os.environ.get("CAMERA_DEVICE")
    if explicit:
        return explicit
    # USB camera identity stays stable when Linux changes /dev/video numbers.
    for device in sorted(glob.glob("/dev/v4l/by-id/*-video-index0")):
        if os.path.exists(device):
            return device
    for device in ("/dev/video0", "/dev/video1"):
        if os.path.exists(device):
            return device
    return "/dev/video0"


HAND_CONNECTIONS = ((0,1),(1,2),(2,3),(3,4),(0,5),(5,6),(6,7),(7,8),
                    (5,9),(9,10),(10,11),(11,12),(9,13),(13,14),(14,15),
                    (15,16),(13,17),(0,17),(17,18),(18,19),(19,20))


def overlay_tensor_indices(outputs, fallback_score):
    # Drawing requires image coordinates, never the world-landmark tensor.
    candidates = [d for d in outputs if np.prod(d['shape']) == 63]
    named = {d['name'].split(':')[0].split('/')[-1]: d for d in outputs}
    image = next((named[n] for n in ('Identity', 'landmarks', 'image_landmarks')
                  if n in named and np.prod(named[n]['shape']) == 63), None)
    if image is None and len(candidates) == 1:
        image = candidates[0]
    presence = named.get('Identity_1')
    score = presence['index'] if presence is not None and np.prod(presence['shape']) == 1 else fallback_score
    return (None if image is None else image['index']), score


def overlay_points(raw, box, input_size):
    points = np.asarray(raw, dtype=np.float64).reshape(21,3)
    if not np.isfinite(points).all():
        return None
    x1,y1,x2,y2 = box
    width,height = input_size
    xy = points[:,:2].copy()
    xy[:,0] = x1 + xy[:,0] / width * (x2-x1)
    xy[:,1] = y1 + xy[:,1] / height * (y2-y1)
    return xy


def draw_hand_overlay(frame, points):
    display = frame.copy()
    if points is None:
        return display
    points = np.asarray(points)
    if points.shape != (21,2) or not np.isfinite(points).all():
        return display
    h,w = frame.shape[:2]
    inside = (points[:,0]>=0)&(points[:,0]<w)&(points[:,1]>=0)&(points[:,1]<h)
    xy = np.rint(np.clip(points,-100000,100000)).astype(int)
    for first,last in HAND_CONNECTIONS:
        if inside[first] and inside[last]:
            cv2.line(display,tuple(xy[first]),tuple(xy[last]),(0,220,0),2,cv2.LINE_AA)
    for index in np.flatnonzero(inside):
        cv2.circle(display,tuple(xy[index]),3,(0,80,255),-1,cv2.LINE_AA)
    return display


def result_is_timely(now, captured, completed):
    # Completion freshness and camera age are distinct. Do not rejuvenate an
    # arbitrarily old frame just because inference finished a moment ago.
    return (completed > 0 and captured <= completed <= now
            and now-completed <= .7 and completed-captured <= 1.2
            and now-captured <= 1.5)


class PoseHoldGate:
    """Debounce observations, not GUI ticks. Durations are software defaults."""

    def __init__(self, acquire=0.10, grace=0.6, stale=0.8):
        self.acquire, self.grace, self.stale = acquire, grace, stale
        self.reset()

    def reset(self):
        self.context = None
        self.seq = None
        self.positive_since = None
        self.positive_samples = 0
        self.last_good = float("-inf")
        self.locked = False
        self.current_good = False

    def update(self, now, seq, captured, match, present, healthy, context):
        if context != self.context:
            self.reset()
            self.context = context
        if not healthy or captured > now or now - captured > self.stale:
            self.reset()
            self.context = context
            return False, "paused", False
        # Expire BEFORE ingesting a new observation, so a long gap cannot
        # continue an old lock when a fresh positive sample finally arrives.
        if self.locked and captured - self.last_good > self.grace:
            self.locked = False
            self.positive_since = None
            self.positive_samples = 0
        if seq != self.seq:
            self.seq = seq
            self.current_good = bool(match and present)
            if self.current_good:
                self.last_good = captured
                if self.positive_since is None:
                    self.positive_since = captured
                self.positive_samples += 1
                if self.positive_samples >= 2 and captured - self.positive_since >= self.acquire:
                    self.locked = True
            elif not self.locked:
                self.positive_since = None
                self.positive_samples = 0
        if self.locked and now - self.last_good <= self.grace:
            confirmed = self.current_good and now - captured <= 0.35
            return True, "stable" if confirmed else "grace", confirmed
        if self.locked:
            self.locked = False
            self.positive_since = None
            self.positive_samples = 0
        return False, "acquiring" if self.current_good else "paused", False

def select_hand_outputs(details):
    """Match semantic names or the official MediaPipe Identity export contract.

    Unknown/ambiguous exports fail visibly instead of treating handedness as
    hand presence or world coordinates as image pixel coordinates.
    """
    import re
    def size(d):
        return int(np.prod(d["shape"]))
    def name(d):
        return d["name"].lower().split(":")[0].split("/")[-1]
    named_landmarks = [d for d in details if size(d) == 63 and
                       ("ld_21_3d" in name(d) or
                        ("landmark" in name(d) and "world" not in name(d)))]
    named_presence = [d for d in details if size(d) == 1 and
                      any(word in name(d) for word in ("handflag", "presence", "hand_flag"))]
    named_handedness = [d for d in details if size(d) == 1 and "handedness" in name(d)]
    if len(named_landmarks) == len(named_presence) == 1:
        return (named_landmarks[0], named_presence[0],
                named_handedness[0] if len(named_handedness) == 1 else None)
    identities = {name(d): d for d in details if re.fullmatch(r"identity(?:_[123])?", name(d))}
    if (len(details) in (3, 4) and len(identities) == len(details)
            and all(key in identities for key in ("identity", "identity_1", "identity_2"))
            and size(identities["identity"]) == 63
            and size(identities["identity_1"]) == size(identities["identity_2"]) == 1
            and (len(details) == 3 or size(identities["identity_3"]) == 63)):
        return identities["identity"], identities["identity_1"], identities["identity_2"]
    # Older exports with exactly one landmark and one scalar are unambiguous.
    vectors = [d for d in details if size(d) == 63]
    scalars = [d for d in details if size(d) == 1]
    if len(details) == 2 and len(vectors) == len(scalars) == 1:
        return vectors[0], scalars[0], None
    summary = [(d["index"], d["name"], list(d["shape"])) for d in details]
    raise ValueError(f"Unknown hand model output mapping; inspect model: {summary}")


def handedness_label(left_score):
    """MediaPipe binary output is P(Left) for a horizontally mirrored image.

    Leave the uncertain middle unclassified so it cannot advance an exercise.
    The camera worker already mirrors frames before inference.
    """
    if not np.isfinite(left_score) or not 0 <= left_score <= 1:
        return None
    if left_score >= .60:
        return "ซ้าย"
    if left_score <= .40:
        return "ขวา"
    return None


def ensure_handedness_model(factory, primary, directory, threads):
    """Use the bundled task's landmark model if the active model lacks a side output."""
    import hashlib
    import zipfile
    _, _, side = select_hand_outputs(primary.get_output_details())
    if side is not None:
        logging.info("Handedness output: %s", side['name'])
        return primary
    logging.warning("Active landmark model has no handedness output; checking bundled model")
    sources = [(os.path.join(directory,"hand_landmarker.task"),True),
               (os.path.join(directory,"hand_landmarks_detector.tflite"),False),
               (os.path.join(directory,"models","hand_landmarks_detector.tflite"),False)]
    for path, archived in sources:
        if not os.path.isfile(path):
            continue
        try:
            if archived:
                with zipfile.ZipFile(path) as task:
                    data = task.read("hand_landmarks_detector.tflite")
            else:
                with open(path,"rb") as source:
                    data = source.read()
            candidate = factory(model_content=data,num_threads=threads)
            candidate.allocate_tensors()
            inputs = candidate.get_input_details()
            _, _, side = select_hand_outputs(candidate.get_output_details())
            if (len(inputs) != 1 or inputs[0]['dtype'] != np.float32
                    or len(inputs[0]['shape']) != 4 or inputs[0]['shape'][1] != inputs[0]['shape'][2]
                    or side is None):
                raise ValueError("Bundled landmark model has no compatible handedness output")
            logging.info("Using landmark model with handedness: %s%s sha256=%s output=%s",
                         path, ":hand_landmarks_detector.tflite" if archived else "",
                         hashlib.sha256(data).hexdigest(),side['name'])
            return candidate
        except Exception:
            logging.exception("Cannot use landmark model from %s",path)
    logging.error("No model can identify left/right; exercise timer will remain paused")
    return primary

def comfortable_pose_match(points, pose, margin=6.0):
    """Small software tolerance around the original ranges, not clinical criteria."""
    low, high = {1:(120,200),2:(15,170),3:(0,110),4:(0,140),5:(30,180)}.get(pose,(120,200))
    count = 0
    for tip,base in ((8,5),(12,9),(16,13),(20,17)):
        first, second = points[tip]-points[base], points[0]-points[base]
        norm = float(np.linalg.norm(first)*np.linalg.norm(second))
        if norm <= 1e-6:
            continue
        angle = math.degrees(math.acos(float(np.clip(np.dot(first,second)/norm,-1,1))))
        count += max(0,low-margin) <= angle <= min(180,high+margin)
    return count >= 3


class HandPresenceLatch:
    """Brief display-only tolerance; never refresh from repeated GUI reads."""
    def __init__(self):
        self.last_seen = float('-inf')
        self.seq = None
    def update(self, now, seq, captured, present, healthy):
        if not healthy or not 0 <= now-captured < .8:
            self.last_seen = float('-inf')
            self.seq = seq
            return False
        if seq != self.seq:
            self.seq = seq
            if present:
                self.last_seen = captured
        return 0 <= now-self.last_seen <= 1.0


class LegacyLocalTracker:
    """Reuse the working model/crop path; bounded local search, no extra models."""
    def __init__(self, interpreter):
        self.model = interpreter
        inputs = interpreter.get_input_details()
        image, presence, handedness = select_hand_outputs(interpreter.get_output_details())
        if len(inputs)!=1 or inputs[0]['dtype']!=np.float32:
            raise ValueError('Expected the original float32 hand model')
        self.input = inputs[0]['index']
        self.height,self.width = map(int,inputs[0]['shape'][1:3])
        self.image,self.presence = image['index'],presence['index']
        self.handedness = handedness['index'] if handedness is not None else None
        logging.info('Hand outputs: image=%s presence=%s handedness=%s',
                     image['name'],presence['name'],
                     handedness['name'] if handedness is not None else 'unavailable')
        self.box = None
        self.last_points = None
        self.last_seen = float('-inf')
        self.last_good = float('-inf')
        self.last_pose = None
        self.track_id = 0
        self.search_index = 0
        self.pending_box = None
        self.next_box_trial = 0.0
        self.retry_previous = False
        self.misses = 0
        self.last_score = float('nan')
        self.last_reason = "starting"
        self.last_hand = None
        self.last_handedness_score = float('nan')

    @staticmethod
    def bounded_box(center, side, shape):
        h,w = shape[:2]
        cx,cy = center
        return (max(0,int(cx-side/2)),max(0,int(cy-side/2)),
                min(w,int(cx+side/2)),min(h,int(cy+side/2)))

    def search_box(self, frame):
        # Preserve the known working dark-contour proposal, but don't let a
        # bright background or a wrong large shadow veto all inference.
        h,w = frame.shape[:2]
        gray = cv2.cvtColor(frame,cv2.COLOR_BGR2GRAY)
        _,mask = cv2.threshold(cv2.GaussianBlur(gray,(5,5),0),70,255,cv2.THRESH_BINARY_INV)
        contours,_ = cv2.findContours(mask,cv2.RETR_EXTERNAL,cv2.CHAIN_APPROX_SIMPLE)
        candidates=[(0,0,w,h)]
        for contour in sorted(contours,key=cv2.contourArea,reverse=True)[:3]:
            if 1500 < cv2.contourArea(contour) < h*w*.95:
                x,y,cw,ch = cv2.boundingRect(contour)
                candidates.append(self.bounded_box((x+cw/2,y+ch/2),max(cw,ch)*1.6,frame.shape))
        # Overlapping local views help acquisition when the hand occupies only
        # part of the full image. Still only one search inference per sample.
        for fraction in (.25,.5,.75):
            candidates.append(self.bounded_box((w*fraction,h*.5),h*.95,frame.shape))
        result = candidates[self.search_index % len(candidates)]
        self.search_index += 1
        return result

    def infer(self, frame, box, threshold):
        x1,y1,x2,y2 = box
        crop = frame[y1:y2,x1:x2]
        if min(crop.shape[:2]) < 32:
            return None
        # Keep the hand proportions intact even for a tall/narrow crop.
        side=max(crop.shape[:2])
        left=(side-crop.shape[1])//2
        top=(side-crop.shape[0])//2
        padded=cv2.copyMakeBorder(crop,top,side-crop.shape[0]-top,
                                 left,side-crop.shape[1]-left,cv2.BORDER_CONSTANT,value=(0,0,0))
        data = cv2.resize(cv2.cvtColor(padded,cv2.COLOR_BGR2RGB),(self.width,self.height))
        self.model.set_tensor(self.input,data.astype(np.float32)[None]/255.0)
        self.model.invoke()
        score = float(self.model.get_tensor(self.presence).reshape(-1)[0])
        self.last_score = score
        if not np.isfinite(score) or not threshold <= score <= 1:
            self.last_reason = "low_presence"
            return None
        raw = np.asarray(self.model.get_tensor(self.image),dtype=np.float32).reshape(21,3)
        if not np.isfinite(raw).all():
            self.last_reason = "invalid_points"
            return None
        points = raw.copy()
        points[:,0] = x1-left + raw[:,0]*side/self.width
        points[:,1] = y1-top + raw[:,1]*side/self.height
        points[:,2] = raw[:,2]*side/self.width
        h,w=frame.shape[:2]
        visible=(points[:,0]>=0)&(points[:,0]<w)&(points[:,1]>=0)&(points[:,1]<h)
        palm=float(np.linalg.norm(points[9,:2]-points[0,:2]))
        # Seeing a hand does not require all fingertips to be usable for pose
        # assessment. Keep that stricter check below, exclusively for timing.
        if visible.sum()<8 or not 2<palm<max(w,h):
            self.last_reason = "point_geometry"
            return None
        if self.handedness is not None:
            self.last_handedness_score = float(self.model.get_tensor(self.handedness).reshape(-1)[0])
            self.last_hand = handedness_label(self.last_handedness_score)
        self.last_reason = "found"
        return points

    def process(self, frame, captured, pose):
        h, w = frame.shape[:2]
        # Keep the last successful crop through transient low-presence results.
        # The v4 code cleared it after one miss, which made acquisition rotate
        # through unrelated full-frame tiles and caused long YES/NO oscillation.
        if self.box is not None and captured - self.last_seen <= 2.0:
            x1, y1, x2, y2 = self.box
            cx, cy = (x1+x2)/2, (y1+y2)/2
            base_side = max(x2-x1, y2-y1)
            recovery = self.misses % 6
            if recovery in (0, 1, 3):
                used_box = self.box
            elif recovery == 2:
                used_box = self.bounded_box((cx,cy), base_side*1.25, frame.shape)
            elif recovery == 4:
                used_box = self.bounded_box((cx,cy), base_side*1.55, frame.shape)
            else:
                used_box = self.search_box(frame)
            threshold = .40 if captured-self.last_seen <= 1.0 else .50
        else:
            used_box = self.search_box(frame)
            threshold = .50

        # One inference per new camera sample. Recovery choices are tried on
        # subsequent fresh frames, avoiding the old 800-890 ms double invokes.
        points = self.infer(frame, used_box, threshold)
        if points is None:
            self.misses += 1
            self.last_reason += f"_miss{self.misses}"
            if captured-self.last_seen > 2.0:
                self.box = None
            return None, False, self.track_id

        was_tracking = self.box is not None and captured-self.last_seen <= 2.0
        self.misses = 0
        self.box = used_box
        span=max(float(np.ptp(points[:,0])),float(np.ptp(points[:,1])),40.0)
        same=(self.last_points is not None and captured-self.last_seen<=2.0
              and np.linalg.norm(points[0,:2]-self.last_points[0,:2])<span*.75)
        if same:
            alpha=1-math.exp(-max(0,captured-self.last_seen)/.075)
            filtered=self.last_points+alpha*(points-self.last_points)
        else:
            self.track_id+=1
            self.last_good=float('-inf')
            filtered=points

        # Recenter gradually only when the hand approaches the crop border.
        center=(points[:,:2].min(axis=0)+points[:,:2].max(axis=0))/2
        proposed=self.bounded_box(center,span*1.85,frame.shape)
        x1,y1,x2,y2=self.box
        inset=min(x2-x1,y2-y1)*.10
        near_border=(points[:,0].min()<x1+inset or points[:,0].max()>x2-inset
                     or points[:,1].min()<y1+inset or points[:,1].max()>y2-inset)
        if near_border:
            old=np.asarray(self.box,dtype=float)
            new=np.asarray(proposed,dtype=float)
            self.box=tuple(np.rint(old*.65+new*.35).astype(int))

        margin=10.0 if self.last_pose==pose and captured-self.last_good<=.6 else 6.0
        visible=(points[:,0]>=0)&(points[:,0]<w)&(points[:,1]>=0)&(points[:,1]<h)
        pose_usable=bool(visible[[0,4,8,12,16,20]].all() and visible.sum()>=19)
        matched=pose_usable and comfortable_pose_match(filtered,pose,margin)
        if matched:
            self.last_good=captured
        self.last_points=filtered.copy()
        self.last_seen=captured
        self.last_pose=pose
        self.last_reason = "found_tracking" if was_tracking else "found_acquired"
        return filtered,matched,self.track_id


from dataclasses import dataclass


@dataclass(frozen=True)
class ROI:
    cx: float
    cy: float
    side: float
    angle: float  # clockwise radians in image coordinates


@dataclass(frozen=True)
class Palm:
    score: float
    center: np.ndarray
    size: np.ndarray
    keypoints: np.ndarray


def rotation(angle):
    c, s = math.cos(angle), math.sin(angle)
    return np.array([[c, -s], [s, c]], dtype=np.float64)


def hand_angle(wrist, middle):
    delta = np.asarray(middle) - wrist
    if np.linalg.norm(delta) < 1e-6:
        raise ValueError("Degenerate wrist-to-palm direction")
    angle = math.atan2(float(delta[1]), float(delta[0])) + math.pi / 2
    return (angle + math.pi) % (2 * math.pi) - math.pi


def crop_matrix(roi, size):
    """Source pixels -> canonical upright model pixels, including edge padding."""
    if not np.isfinite([roi.cx, roi.cy, roi.side, roi.angle]).all() or roi.side <= 1:
        raise ValueError("Invalid hand ROI")
    linear = rotation(roi.angle).T * (size / roi.side)
    offset = np.array([size / 2, size / 2]) - linear @ [roi.cx, roi.cy]
    return np.column_stack((linear, offset))


def model_tensor(frame, roi, size):
    crop = cv2.warpAffine(frame, crop_matrix(roi, size), (size, size),
                          flags=cv2.INTER_LINEAR, borderMode=cv2.BORDER_CONSTANT,
                          borderValue=(0, 0, 0))
    rgb = cv2.cvtColor(crop, cv2.COLOR_BGR2RGB)
    return rgb.astype(np.float32)[None] / 255.0


def project_landmarks(raw, roi, size=224):
    points = np.asarray(raw, dtype=np.float64).reshape(21, 3).copy()
    if not np.isfinite(points).all():
        raise ValueError("Invalid landmark coordinates")
    local = (points[:, :2] / size - 0.5) * roi.side
    points[:, :2] = local @ rotation(roi.angle).T + [roi.cx, roi.cy]
    points[:, 2] *= roi.side / size
    return points.astype(np.float32)


def make_palm_anchors():
    # Fixed-size anchors: stride 8 has 2 anchors/cell; the three stride-16
    # layers share positions and contribute 6 anchors/cell (2016 in total).
    return np.array([((x + .5) / grid, (y + .5) / grid)
                     for grid, repeats in ((24, 2), (12, 6))
                     for y in range(grid) for x in range(grid)
                     for _ in range(repeats)], dtype=np.float32)


def box_iou(one, many):
    one_min, one_max = one[:2] - one[2:4]/2, one[:2] + one[2:4]/2
    many_min, many_max = many[:, :2] - many[:, 2:4]/2, many[:, :2] + many[:, 2:4]/2
    intersection = np.maximum(0, np.minimum(one_max, many_max) - np.maximum(one_min, many_min)).prod(axis=1)
    union = np.prod(one[2:4]) + np.prod(many[:, 2:4], axis=1) - intersection
    return intersection / np.maximum(union, 1e-9)


def decode_palms(raw_boxes, raw_scores, frame_shape, threshold=.5, max_palms=2):
    boxes = np.asarray(raw_boxes, dtype=np.float32).reshape(2016, 18).copy()
    logits = np.asarray(raw_scores, dtype=np.float32).reshape(2016)
    scores = 1.0 / (1.0 + np.exp(-np.clip(logits, -80, 80)))
    valid = np.isfinite(boxes).all(axis=1) & np.isfinite(logits) & (scores >= threshold)
    anchors = make_palm_anchors()
    boxes[:, :2] = boxes[:, :2] / 192.0 + anchors
    boxes[:, 2:4] /= 192.0
    boxes[:, 4:] = (boxes[:, 4:].reshape(-1, 7, 2) / 192.0 + anchors[:, None, :]).reshape(-1, 14)
    valid &= (boxes[:, 2:4] > 0).all(axis=1)
    valid &= (np.abs(boxes) < 10).all(axis=1)
    h, w = frame_shape[:2]
    side = max(w, h)
    offset = np.array([(w - side)/2, (h - side)/2])
    centers = boxes[:, :2] * side + offset
    valid &= ((centers[:,0] >= 0) & (centers[:,0] < w) &
              (centers[:,1] >= 0) & (centers[:,1] < h))
    indices = np.flatnonzero(valid)
    indices = indices[np.argsort(scores[indices])[::-1]][:200]
    merged = []
    while len(indices) and len(merged) < max_palms:
        first = indices[0]
        overlaps = box_iou(boxes[first], boxes[indices]) > .3
        overlaps[0] = True  # Always consume at least one, including tiny boxes.
        cluster = indices[overlaps]
        weights = scores[cluster]
        merged.append((float(scores[first]), np.average(boxes[cluster], axis=0, weights=weights)))
        indices = indices[~overlaps]
    h, w = frame_shape[:2]
    side = max(w, h)
    offset = np.array([(w - side)/2, (h - side)/2])
    result = []
    for score, box in merged:
        center = box[:2] * side + offset
        if not (0 <= center[0] < w and 0 <= center[1] < h):
            continue  # Discard detections whose center is in letterbox padding.
        result.append(Palm(score, center, box[2:4] * side,
                           box[4:].reshape(7, 2) * side + offset))
    return result


def palm_roi(palm):
    angle = hand_angle(palm.keypoints[0], palm.keypoints[2])
    center = palm.center + rotation(angle) @ [0, -.5 * palm.size[1]]
    return ROI(float(center[0]), float(center[1]), float(max(palm.size) * 2.6), angle)


def landmarks_roi(points):
    points = np.asarray(points)[:, :2]
    # Use the same palm/proximal subset as MediaPipe's tracking rectangle;
    # finger curling should not reverse the wrist-to-palm orientation.
    middle = (points[5] + 2 * points[9] + points[13]) / 4
    angle = hand_angle(points[0], middle)
    subset = points[[0, 1, 2, 3, 5, 6, 9, 10, 13, 14, 17, 18]]
    local = subset @ rotation(angle)
    low, high = local.min(axis=0), local.max(axis=0)
    center_local = (low + high) / 2 + [0, -.1 * (high[1] - low[1])]
    center = center_local @ rotation(angle).T
    side = max(float(max(high - low) * 2), 10.0)
    return ROI(float(center[0]), float(center[1]), side, angle)


class PalmDetector:
    """Float32 MediaPipe palm model, owned only by the inference worker."""
    def __init__(self, interpreter):
        self.model = interpreter
        inputs, outputs = interpreter.get_input_details(), interpreter.get_output_details()
        if (len(inputs) != 1 or tuple(inputs[0]['shape']) != (1,192,192,3)
                or inputs[0]['dtype'] != np.float32):
            raise ValueError('Expected float32 palm input [1,192,192,3]')
        boxes = [d for d in outputs if tuple(d['shape']) == (1,2016,18)]
        scores = [d for d in outputs if tuple(d['shape']) == (1,2016,1)]
        if len(boxes) != 1 or len(scores) != 1:
            raise ValueError('Unsupported palm output shapes')
        self.input = inputs[0]['index']
        self.boxes, self.scores = boxes[0]['index'], scores[0]['index']

    def detect(self, frame):
        h,w = frame.shape[:2]
        self.model.set_tensor(self.input, model_tensor(frame, ROI(w/2,h/2,max(w,h),0),192))
        self.model.invoke()
        return decode_palms(self.model.get_tensor(self.boxes),
                            self.model.get_tensor(self.scores),frame.shape)


def load_palm_detector(factory, directory, threads):
    """Use bundled assets; no network, model installation or extraction on Pi."""
    import hashlib
    import zipfile
    if os.environ.get('HAND_TRACKER','palm').lower() == 'legacy':
        logging.warning('Hand tracker: legacy mode requested')
        return None
    sources = [(os.path.join(directory, 'hand_detector.tflite'), False),
               (os.path.join(directory, 'models', 'hand_detector.tflite'), False),
               (os.path.join(directory, 'hand_landmarker.task'), True)]
    for path, archive in sources:
        if not os.path.isfile(path):
            continue
        try:
            if archive:
                with zipfile.ZipFile(path) as task:
                    data = task.read('hand_detector.tflite')
            else:
                with open(path,'rb') as source:
                    data = source.read()
            model = factory(model_content=data,num_threads=threads)
            model.allocate_tensors()
            detector = PalmDetector(model)
            logging.info('Palm model: %s%s sha256=%s',path,
                         ':hand_detector.tflite' if archive else '',
                         hashlib.sha256(data).hexdigest())
            return detector
        except Exception:
            logging.exception('Cannot load palm model from %s; trying next bundled asset',path)
    logging.warning('Palm model unavailable: using v5 crop tracker. Keep hand_landmarker.task beside main.py for palm recovery.')
    return None


class StableLocalTracker(LegacyLocalTracker):
    """Locate palms, then follow a square, rotation-aligned hand crop.

    Healthy frames invoke only the original landmark model. Recovery uses at
    most one palm invocation and one landmark invocation per fresh camera frame.
    The legacy path is retained for installations without the bundled task file.
    """
    def __init__(self, interpreter, detector=None):
        super().__init__(interpreter)
        if self.width != self.height:
            raise ValueError('Expected square landmark model input')
        self.detector = detector
        self.roi = self.good_roi = None
        self.last_raw = None
        self.palm_calls = self.hand_calls = 0
        self.last_palm_score = float('nan')
        self.stage = 'starting'
        self.palm_choice = 0

    def infer_roi(self, frame, roi, threshold):
        h,w = frame.shape[:2]
        if not np.isfinite([roi.cx,roi.cy,roi.side,roi.angle]).all() or not 16 <= roi.side <= 3*max(w,h):
            self.last_reason = 'invalid_roi'
            return None
        self.model.set_tensor(self.input, model_tensor(frame,roi,self.width))
        self.model.invoke()
        self.hand_calls += 1
        self.last_score = float(self.model.get_tensor(self.presence).reshape(-1)[0])
        if not np.isfinite(self.last_score) or not threshold <= self.last_score <= 1:
            self.last_reason = 'low_presence'
            return None
        try:
            points = project_landmarks(self.model.get_tensor(self.image),roi,self.width)
            proposal = landmarks_roi(points)
        except ValueError:
            self.last_reason = 'invalid_points'
            return None
        visible = (points[:,0]>=0)&(points[:,0]<w)&(points[:,1]>=0)&(points[:,1]<h)
        palm = float(np.linalg.norm(points[9,:2]-points[0,:2]))
        if visible.sum()<8 or not 2<palm<max(w,h) or not 16<=proposal.side<=3*max(w,h):
            self.last_reason = 'point_geometry'
            return None
        if self.handedness is not None:
            self.last_handedness_score = float(self.model.get_tensor(self.handedness).reshape(-1)[0])
            self.last_hand = handedness_label(self.last_handedness_score)
        return points,proposal

    def _miss(self):
        self.misses += 1
        return None,False,self.track_id

    def process(self, frame, captured, pose, target=None):
        self.last_score = self.last_palm_score = float('nan')
        self.last_hand = None
        self.last_handedness_score = float('nan')
        if self.detector is None:
            self.stage = 'legacy'
            result = super().process(frame,captured,pose)
            self.hand_calls += 1
            self.last_reason = self.last_reason.split('_miss')[0]
            if result[0] is not None and target is not None and self.last_hand != target:
                # Do not keep following the other hand while the selected one
                # may be elsewhere in the frame.
                self.box = self.last_points = None
                self.last_seen = float('-inf')
                self.last_good = float('-inf')
                self.last_pose = None
                self.search_index += 1
                self.last_reason = 'found_wrong_hand' if self.last_hand else 'found_side_unknown'
                return result[0],False,result[2]
            return result
        h,w = frame.shape[:2]
        recent = self.roi is not None and 0<=captured-self.last_seen<=1.0
        if recent and self.misses < 3:
            if self.misses == 0:
                used_roi,self.stage = self.roi,'track'
            elif self.misses == 1:
                used_roi,self.stage = self.good_roi,'retry_good'
            else:
                old = self.good_roi
                used_roi = ROI(old.cx,old.cy,old.side*1.15,old.angle)
                self.stage = 'expand'
            threshold = .40
        else:
            self.stage = 'palm'
            self.palm_calls += 1
            palms = self.detector.detect(frame)
            if palms:
                # Prefer the existing hand on recovery; rotate candidates after
                # failures so a high-score unusable palm cannot starve another.
                if self.last_raw is not None and captured-self.last_seen<=1.0:
                    palms = sorted(palms,key=lambda p:np.linalg.norm(p.keypoints[0]-self.last_raw[0,:2]))
                palm = palms[self.palm_choice % len(palms)]
                self.last_palm_score = palm.score
                try:
                    used_roi = palm_roi(palm)
                except ValueError:
                    self.last_reason = 'invalid_palm'
                    self.palm_choice += 1
                    return self._miss()
                threshold = .50
            elif self.misses % 4 == 3:
                # Side-on hands sometimes lack a visible palm. Retain the
                # working v5 proposal as an occasional, stricter fallback.
                x1,y1,x2,y2 = self.search_box(frame)
                used_roi = ROI((x1+x2)/2,(y1+y2)/2,max(x2-x1,y2-y1),0)
                self.stage = 'fallback'
                threshold = .65
            else:
                self.last_reason = 'no_palm'
                return self._miss()
        observation = self.infer_roi(frame,used_roi,threshold)
        if observation is None:
            if self.stage == 'palm':
                self.palm_choice += 1
            return self._miss()
        points,proposal = observation
        span = max(float(np.ptp(points[:,0])),float(np.ptp(points[:,1])),40.0)
        same = (self.last_raw is not None and 0<=captured-self.last_seen<=1.0
                and np.linalg.norm(points[0,:2]-self.last_raw[0,:2])<span*.75)
        dt = max(0,captured-self.last_seen) if same else 0
        if same:
            alpha = 1-math.exp(-dt/.10)
            filtered = self.last_points+alpha*(points-self.last_points)
        else:
            self.track_id += 1
            self.last_good = float('-inf')
            filtered = points

        # Follow each successful frame, using palm/proximal joints so a curled
        # fingertip cannot collapse or reverse the next crop. Never clip the
        # square at the frame edge: warpAffine supplies consistent padding.
        if self.last_score >= .50:
            blend = 1-math.exp(-dt/.08) if same and self.misses==0 else 1.0
            delta = (proposal.angle-used_roi.angle+math.pi)%(2*math.pi)-math.pi
            self.roi = ROI(used_roi.cx+blend*(proposal.cx-used_roi.cx),
                           used_roi.cy+blend*(proposal.cy-used_roi.cy),
                           used_roi.side+blend*(proposal.side-used_roi.side),
                           used_roi.angle+blend*delta)
            self.good_roi = used_roi
        else:
            # Weak but acceptable presence may sustain tracking, but must not
            # cumulatively move the crop based on uncertain landmark positions.
            self.roi = self.good_roi or used_roi
        margin = 10.0 if self.last_pose==pose and captured-self.last_good<=.6 else 6.0
        visible = (points[:,0]>=0)&(points[:,0]<w)&(points[:,1]>=0)&(points[:,1]<h)
        usable = bool(visible[[0,4,8,12,16,20]].all() and visible.sum()>=19)
        matched = usable and comfortable_pose_match(filtered,pose,margin)
        if matched:
            self.last_good = captured
        self.last_raw,self.last_points = points.copy(),filtered.copy()
        self.last_seen,self.last_pose = captured,pose
        prior_choice = self.palm_choice
        self.misses = self.palm_choice = 0
        self.last_reason = 'found_match' if matched else 'found_pose_no' if usable else 'found_edge'
        if target is not None and self.last_hand != target:
            # Search again on the next fresh frame. With two palms in view,
            # palm_choice tries the other candidate instead of staying on this
            # higher-scoring but wrong hand indefinitely.
            self.roi = self.good_roi = None
            self.last_raw = self.last_points = None
            self.last_seen = float('-inf')
            self.last_good = float('-inf')
            self.last_pose = None
            self.palm_choice = prior_choice + 1
            self.last_reason = 'found_wrong_hand' if self.last_hand else 'found_side_unknown'
            matched = False
        return filtered,matched,self.track_id

    def roi_description(self):
        if self.roi is None:
            return '-'
        return '%.0f,%.0f,%.0f,%.0f' % (self.roi.cx,self.roi.cy,self.roi.side,math.degrees(self.roi.angle))



class AntiTriggerFingersApp(ctk.CTk):

    def __init__(self):
        super().__init__()
        # Hide the window while it is being built (no flashing half-drawn layout),
        # and show a simple full-screen splash straight away instead.
        self.withdraw()
        self._splash = self._show_splash()
        global _PROMPT_READY
        try:
            from tkinter import font as tkfont
            families = set(tkfont.families(self))
            _PROMPT_READY = "Prompt TH" in families
            if _PROMPT_READY:
                # Dialogs (messagebox) use Tk's named fonts; they need the
                # same font so the raised tone marks exist there too.
                for name in tkfont.names(self):
                    tkfont.nametofont(name, root=self).configure(family="Prompt TH")
        except Exception:
            _PROMPT_READY = False
        if _PROMPT_READY:
            logging.info("Thai UI font: Prompt TH")
        else:
            logging.error("Thai UI font: Prompt TH not found in %s; falling back to Sarabun", FONT_DIR)
            self.after(1500, lambda: self.show_dialog(
                "Prompt TH font missing",
                f"Prompt TH font not found.\nCheck the folder:\n{FONT_DIR}\nthen restart the program.", "warning"))
        self._localized_labels = []
        self._last_feedback = ("รอตรวจจับท่าทาง...", "Show your hand", "#7F8C8D")
        self._last_breathing = ("เตรียมพร้อมหายใจ...", "Get ready", "#52667A")
        self._pain_button_saved = False
        self._voice_condition = threading.Condition()
        self._voice_pending = None
        self._voice_revision = 0
        self._voice_stopping = False
        self._voice_warning_shown = False
        
        self.screen_width = self.winfo_screenwidth()
        self.screen_height = self.winfo_screenheight()
        
        base_w = 1920
        base_h = 1080

        self.scale_w = self.screen_width / base_w
        self.scale_h = self.screen_height / base_h
        self.u_scale = min(self.scale_w, self.scale_h)
        set_font_scale(self.screen_width, self.screen_height)
        logging.info("Font scale: %.2f", FONT_SCALE)

        self.title("Finger Exercise Coach")
        self.bind("<Escape>", lambda e: self.on_close())
        self.configure(fg_color="#F4F7F6") 

        self.target_sets_var = tk.IntVar(value=1)
        self.target_hand_var = ctk.StringVar(value="ซ้าย")

        self.key_held = False
        self.time_max = 5
        self.time_current = self.time_max
        self.hand_posit = 0
        self.still_hold = False
        self.current_pose = 1
        self.key = ""
        self.is_pass = False
        self.round = 0
        self.set = 0
        self.completed_sets = []
        self._web_server = web_report.ReportServer(
            os.path.join(os.path.dirname(os.path.abspath(__file__)), "web_reports"))
        self._qr_popup = None
        self._report_started_at = datetime.now().astimezone()
        self._last_report_expiry_check = time.monotonic()
        self._last_live_report_update = 0.0
        self._last_pain = None
        self._pain_before = None
        self._pain_after = None
        self._load_report_state()
        self._prune_activity_log()
        self.set = len(self.completed_sets)
        self._set_stable_poses = 0
        saved = getattr(self, "_saved_progress", None)
        if saved:
            # Resume where the last session stopped inside an unfinished set.
            self.round, self.current_pose = saved["round"], saved["pose"]
            stable = saved.get("stable_poses")
            self._set_stable_poses = stable if type(stable) is int and 0 <= stable <= 15 else 0
            if saved.get("hand") in ("ซ้าย", "ขวา"):
                self.target_hand_var.set(saved["hand"])
        # Save only after restoring, otherwise an unfinished set was lost on restart.
        self._save_report_state()
        self._pose_had_long_pause = False
        self._pose_pause_started = None
        self._daily_pose_cache_time = 0.0
        self._daily_pose_counts = []
        self._goal_reached = False  # kept for compatibility; sets are unlimited now
        

        self.pose_name = [
            "placeholder",
            "เหยียดมือตรง",
            "ทำมือคล้ายตะขอ",
            "กำมือ",
            "กำมือแบบเหยียดปลายนิ้ว",
            "งอโคนนิ้วแต่เหยียดปลายนิ้วมือ" 
        ]
        self.pose_name_en = ["", "Straight fingers", "Hook fist", "Full fist", "Straight fist", "Tabletop"]
        self.pose_labels_th = ["", "เหยียดนิ้วตรง", "มือรูปตะขอ", "กำมือ", "กำมือปลายนิ้วตรง", "งอโคนนิ้ว เหยียดนิ้ว"]

        # Only the capture worker opens, reads and releases the device.
        self.camera_path = choose_camera_device()
        self._stop_video = threading.Event()
        self.frame_lock = threading.Lock()
        self.latest_frame = None
        self.frame_seq = 0
        self.frame_time = 0.0
        self.latest_match = False
        self.latest_overlay_points = None
        self.overlay_time = 0.0
        self.overlay_completed = 0.0
        self.result_completed = 0.0
        self.latest_present = False
        self.latest_observed_present = False
        self.latest_hand = None
        self.result_seq = -1
        self.result_track_id = 0
        self.ai_target_hand = "ซ้าย"
        self.result_target_hand = None
        self._match_gate = PoseHoldGate()
        self._presence_latch = HandPresenceLatch()
        self._match_confirmed = False
        self._match_state = "paused"
        self._match_updated = 0.0
        self._last_sensor_tick = time.monotonic()
        self.latest_env_text = ui("AI: กำลังเริ่มต้น...", "AI: starting...")
        self.latest_env_color = "#F39C12"
        self.result_time = 0.0
        self.result_pose = None
        self.ai_pose = self.current_pose
        self.camera_error = None
        self.ai_error = None
        self._closing = False
        self._video_job = None
        self._sensor_job = None
        self._displayed_seq = -1
        self._workers = []
        self._preview_only = os.environ.get("CAMERA_PREVIEW_ONLY") == "1"

        self.purple_bg = "#4A235A" 
        self.light_gray_bg = "#FFFFFF" 
        self.light_gray_bg_program = "transparent"
        self.red_btn = "#E74C3C"
        self.hover_red_bt = "#C0392B"
        self.yellow_btn = "#F39C12"
        self.hover_yellow_bt = "#D68910"
        self.green_btn = "#2ECC71"
        self.hover_green_bt = "#27AE60"
        self.blue_btn = "#3498DB"
        self.white_fg = "#ffffff"
        self.black_fg = "#2C3E50"

        self.font_large_title = ui_font(max(26, int(32 * self.u_scale)), "bold")
        self.font_medium_text = ui_font(max(21, int(30 * self.u_scale)), "semibold")
        self.font_timer = ui_font(max(50, int(55 * self.u_scale)), "bold")
        self.font_pose_title = ui_font(max(27, int(28 * self.u_scale)), "semibold")
        self.font_pose_action = ui_font(max(22, int(25 * self.u_scale)), "regular")
        self.font_btn_text = ui_font(max(23, int(22 * self.u_scale)), "semibold")
        self.font_small = ui_font(max(19, int(18 * self.u_scale)), "semibold")
        self.font_feedback = ui_font(max(20, int(18 * self.u_scale)), "regular", max_scale=1.2)

        top_bar_h = max(64, int(105 * self.scale_h))
        logo_size = int(100 * self.u_scale)
        
        self.camera_width = int(self.screen_width * .38) - 24
        self.camera_height = self.screen_height - top_bar_h - 26
        
        self.btn_h = int(65 * self.scale_h) 
        self.btn_w = int(160 * self.scale_w)
        
        self.timer_canvas_size = int(200 * self.u_scale)
        self.timer_pad = 8

        self.top_bar_frame = ctk.CTkFrame(self, fg_color=self.purple_bg, height=top_bar_h, corner_radius=0)
        self.top_bar_frame.pack(side="top", fill="x")
        self.top_bar_frame.pack_propagate(False)

        BASE_DIR = os.path.dirname(os.path.abspath(__file__))
        logo_path = os.path.join(BASE_DIR, "pictures", "logo.png")
        try:
            logo_image_pil = Image.open(logo_path)
            self.logo_photo = ctk.CTkImage(light_image=logo_image_pil, size=(logo_size, logo_size))
            self.logo_label = ctk.CTkLabel(self.top_bar_frame, image=self.logo_photo, text="")
            self.logo_label.pack(side="left", padx=int(20 * self.scale_w), pady=int(10 * self.scale_h))
        except FileNotFoundError:
            self.logo_label = ctk.CTkLabel(self.top_bar_frame, text="LOGO", font=ui_font(18, "semibold"), text_color=self.white_fg)
            self.logo_label.pack(side="left", padx=20, pady=15)

        self.app_title_label = ctk.CTkLabel(
            self.top_bar_frame, text="Finger Exercise Coach", font=self.font_large_title, text_color=self.white_fg
        )
        self.app_title_label.pack(side="left", padx=12, pady=15)

        self.exit_btn = ctk.CTkButton(
            self.top_bar_frame, text="×", font=("Arial", 26, "bold"), fg_color="#68417A", text_color="#FFFFFF",
            hover_color="#84579B", width=50, height=48, corner_radius=14, command=self.on_close
        )
        self.exit_btn.pack(side="right", padx=16, pady=4)
        self.language_button = ctk.CTkButton(
            self.top_bar_frame, text="English", font=self.font_small,
            fg_color="#68417A", text_color="#FFFFFF", hover_color="#84579B",
            width=max(95, int(130 * self.scale_w)), height=max(42, int(55 * self.scale_h)),
            corner_radius=12, command=self.toggle_language)
        self.language_button.pack(side="right", padx=8, pady=4)

        self.main_content_frame = ctk.CTkFrame(self, fg_color=self.light_gray_bg_program)
        self.main_content_frame.pack(side="top", fill="both", expand=True, padx=8, pady=4)
        
        self.camera_frame_bg = ctk.CTkFrame(self.main_content_frame, fg_color=self.light_gray_bg, corner_radius=12, border_width=1, border_color="#D5D8DC")
        self.camera_frame_bg.place(relwidth=.372, x=3, relheight=1)
        self.camera_frame_bg.pack_propagate(False) 
        
        placeholder = Image.new("RGB", (self.camera_width, self.camera_height), (220, 220, 220))
        self.camera_photo = ctk.CTkImage(light_image=placeholder, size=(self.camera_width, self.camera_height))
        self.camera_label = ctk.CTkLabel(self.camera_frame_bg, image=self.camera_photo, text="", corner_radius=12)
        self.camera_label.pack(expand=True, padx=3, pady=3)

        self.match_badge = ctk.CTkLabel(
            self.camera_label, text="กำลังหามือ", font=ui_font(max(21, int(24 * self.u_scale)), "semibold"), 
            fg_color="#FFFFFF", text_color="#E74C3C", corner_radius=6, padx=10, pady=2
        )
        self.match_badge.place(x=15, y=15)
        
        self.env_badge = ctk.CTkLabel(
            self.camera_label, text="ระยะกล้อง/แสง: ตรวจสอบ...", font=ui_font(max(17, int(18 * self.u_scale)), "regular"),
            wraplength=max(250, self.camera_width-35),
            fg_color="#2C3E50", text_color="#FFFFFF", corner_radius=6, padx=6, pady=2
        )
        self.env_badge.place(x=15, y=55)

        self.center_info_container = ctk.CTkFrame(self.main_content_frame, fg_color="transparent")
        self.center_info_container.place(relx=.38, relwidth=.314, relheight=1)
        center_wrap = int(self.screen_width * .32) - 36

        self.set_times_frame = ctk.CTkFrame(self.center_info_container, fg_color=self.light_gray_bg, corner_radius=12, border_width=1, border_color="#D5D8DC")
        self.set_times_frame.place(relwidth=1, relheight=.247)
        self.set_times_frame.pack_propagate(False)

        self.times_line_frame = ctk.CTkFrame(self.set_times_frame, fg_color="transparent")
        self.times_line_frame.pack(side="top", pady=(8, 1))
        
        self.Label_times_text = ctk.CTkLabel(self.times_line_frame, text="รอบที่ : ", font=self.font_medium_text, text_color=self.black_fg)
        self._localized_labels.append((self.Label_times_text, "รอบที่ : ", "Round: "))
        self.Label_times_text.pack(side="left", padx=(14, 0))
        self.Label_set_times_number = ctk.CTkLabel(self.times_line_frame, text=f"{self.round}", font=self.font_medium_text, text_color=self.blue_btn)
        self.Label_set_times_number.pack(side="left", padx=(0, 14))

        self.sets_line_frame = ctk.CTkFrame(self.set_times_frame, fg_color="transparent")
        self.sets_line_frame.pack(side="top", pady=(1, 4))
        
        self.Label_set_text = ctk.CTkLabel(self.sets_line_frame, text="เซตที่ : ", font=self.font_medium_text, text_color=self.black_fg)
        self._localized_labels.append((self.Label_set_text, "เซตที่ : ", "Set: "))
        self.Label_set_text.pack(side="left", padx=(14, 0))
        self.Label_set_number = ctk.CTkLabel(self.sets_line_frame, text=f"{self.set}", font=self.font_medium_text, text_color=self.green_btn)
        self.Label_set_number.pack(side="left", padx=(0, 14))

        self.round_progress = ctk.CTkProgressBar(self.set_times_frame, width=int(280 * self.scale_w), height=14, fg_color="#EAECEE", progress_color=self.green_btn, corner_radius=8)
        self.round_progress.pack(pady=(2, 4))
        self.round_progress.set(0) 
        
        self.reward_label = ctk.CTkLabel(self.set_times_frame, text="พร้อมแล้ว เริ่มฝึกได้", font=ui_font(max(19, int(20 * self.u_scale)), "regular"), text_color="#A45C00")
        self.reward_label.pack(side="top", pady=(0, 4))

        self.pose_text_frame = ctk.CTkFrame(self.center_info_container, fg_color=self.light_gray_bg, corner_radius=12, border_width=1, border_color="#D5D8DC")
        self.pose_text_frame.place(rely=.255, relwidth=1, relheight=.217)
        self.pose_text_frame.pack_propagate(False)
        
        self.Label_pose_thai_text = ctk.CTkLabel(self.pose_text_frame, text=f"ท่าที่ {self.current_pose}", font=self.font_pose_title, text_color=self.black_fg)
        self.Label_pose_thai_text.pack(side="top", pady=(4, 0))
        
        self.Label_pose_action_text = ctk.CTkLabel(
            self.pose_text_frame, text=self.pose_labels_th[self.current_pose], font=self.font_pose_action,
            text_color=self.purple_bg, wraplength=center_wrap
        )
        self.Label_pose_action_text.pack(side="top", pady=(0, 3), padx=8)

        self.pose_feedback_label = ctk.CTkLabel(self.pose_text_frame, text="รอตรวจจับท่าทาง...", font=self.font_feedback, text_color="#52667A", wraplength=center_wrap)
        self.pose_feedback_label.pack(side="top", pady=(0, 3))

        self.popup_menu_frame = ctk.CTkFrame(self.center_info_container, fg_color=self.light_gray_bg, corner_radius=12, border_width=1, border_color="#D5D8DC")
        self.popup_menu_frame.place(rely=.48, relwidth=1, relheight=.172)
        self.popup_menu_frame.pack_propagate(False)

        self.btn_select_hand = ctk.CTkButton(
            self.popup_menu_frame, text=f"มือ{self.target_hand_var.get()} ▾", font=self.font_small,
            fg_color="#E5E7E9", text_color=self.black_fg, hover_color="#BDC3C7", height=max(48,int(58*self.scale_h)), corner_radius=10,
            command=self.open_hand_popup
        )
        self.btn_select_hand.pack(fill="x", padx=12, pady=4)

        self.protocol_label = ctk.CTkLabel(self.popup_menu_frame, text="3 รอบ · ท่าละ 5 วิ",
                                           font=self.font_small, text_color=self.black_fg,
                                           wraplength=center_wrap)
        self.protocol_label.pack(fill="x", padx=12, pady=(4, 8))
        self._localized_labels.append((self.protocol_label, "3 รอบ · ท่าละ 5 วิ",
                                       "3 rounds · 5 sec per pose"))

        self.pain_frame = ctk.CTkFrame(self.center_info_container, fg_color="#FDF2E9", corner_radius=12, border_width=1, border_color="#F5B041")
        self.pain_frame.place(rely=.66, relwidth=1, relheight=.152)
        self.pain_frame.pack_propagate(False)
        
        self.pain_title = ctk.CTkLabel(self.pain_frame, text="ความปวดก่อนฝึก (0-10)", font=ui_font(max(19, int(20 * self.u_scale)), "semibold"), text_color="#9C4300")
        self.pain_title.pack(pady=(4, 0))
        self._localized_labels.append((self.pain_title, "ความปวดก่อนฝึก (0-10)", "Pain before practice (0-10)"))
        
        slider_inner = ctk.CTkFrame(self.pain_frame, fg_color="transparent")
        slider_inner.pack(fill="x", padx=10, pady=(0, 4))
        
        self.pain_var = ctk.IntVar(value=5)
        self.pain_val_lbl = ctk.CTkLabel(slider_inner, text="5", font=ui_font(22, "bold"), text_color="#A22B20", width=35)
        self.pain_val_lbl.pack(side="left", padx=(2, 6))
        
        self.pain_slider = ctk.CTkSlider(slider_inner, from_=0, to=10, number_of_steps=10, variable=self.pain_var, command=lambda v: self.pain_val_lbl.configure(text=int(v)), progress_color="#E74C3C", button_color="#C0392B", height=22, width=80)
        self.pain_slider.pack(side="left", fill="x", expand=True, padx=4)
        
        self.pain_btn = ctk.CTkButton(slider_inner, text="บันทึก", font=self.font_small, fg_color="#B83228", hover_color="#8C251E", width=max(90, int(110 * FONT_SCALE)), height=max(40,int(48 * self.scale_h)), command=self.save_pain_log)
        self.pain_btn.pack(side="right", padx=(8, 2))
        self.pain_saved_banner = ctk.CTkLabel(self.pain_frame, text="", fg_color="#137A4B", corner_radius=12,
                                              text_color="#FFFFFF", font=ui_font(20, "bold"), justify="center")

        self.controls_btn_frame = ctk.CTkFrame(self.center_info_container, fg_color="transparent")
        self.controls_btn_frame.place(rely=.82, relwidth=1, relheight=.172)
        self.controls_btn_frame.pack_propagate(False)
        
        self.start_stop_button = ctk.CTkButton(
            self.controls_btn_frame, text=self._start_label(), font=self.font_btn_text, fg_color=self.green_btn,
            text_color=self.white_fg, command=lambda: self.toggle_start_pause(), height=self.btn_h,
            hover_color=self.hover_green_bt, corner_radius=15
        )
        self.start_stop_button.place(relwidth=1, relheight=.47)
        
        self.reset_button = ctk.CTkButton(
            self.controls_btn_frame, text="รีเซ็ต", font=self.font_btn_text, fg_color=self.red_btn,
            text_color=self.white_fg, command=lambda: self.reset_action(), height=self.btn_h,
            hover_color=self.hover_red_bt, corner_radius=15
        )
        self.reset_button.place(rely=.53, relwidth=1, relheight=.47)

        self.right_info_container = ctk.CTkFrame(self.main_content_frame, fg_color="transparent")
        self.right_info_container.place(relx=.70, relwidth=.297, relheight=1)

        self.timer_frame = ctk.CTkFrame(self.right_info_container, fg_color="transparent")
        self.timer_frame.place(relwidth=1, relheight=.34)
        self.timer_frame.pack_propagate(False)
        
        self.timer_canvas = ctk.CTkCanvas(self.timer_frame, width=self.timer_canvas_size, height=self.timer_canvas_size, bg="#F4F7F6", highlightthickness=0)
        self.timer_canvas.pack(pady=2)
        
        left_p = self.timer_pad
        right_p = self.timer_canvas_size - self.timer_pad
        self.timer_canvas.create_oval(left_p, left_p, right_p, right_p, outline=self.green_btn, width=12, tags="progress")
        center = self.timer_canvas_size // 2
        
        display_time = int(math.ceil(self.time_current))
        self.timer_text = self.timer_canvas.create_text(center, center, text=str(display_time), font=self.font_timer, fill=self.black_fg)

        self.breathing_label = ctk.CTkLabel(self.timer_frame, text="เตรียมพร้อมหายใจ...", font=ui_font(max(19,int(20 * self.u_scale)), "regular"), text_color="#52667A", wraplength=int(self.screen_width * .30) - 28)
        self.breathing_label.pack(pady=(0, 2))

        img_size = self.reference_image_size = min(int(self.screen_width * .27), int(self.camera_height * .51))
        self.small_hand_bg = ctk.CTkFrame(self.right_info_container, fg_color=self.light_gray_bg, corner_radius=12, border_width=1, border_color="#D5D8DC")
        self.small_hand_bg.place(rely=.34, relwidth=1, relheight=.53)
        self.small_hand_bg.pack_propagate(False) 

        try:
            pose_path = os.path.join(BASE_DIR, "pictures", "EX_POSE", "pose1.png")
            small_hand_image_pil = Image.open(pose_path)
            self._reference_missing = False
            self.small_hand_photo = ctk.CTkImage(light_image=small_hand_image_pil, size=(img_size, img_size))
            self.small_hand_label = ctk.CTkLabel(self.small_hand_bg, image=self.small_hand_photo, text="", corner_radius=8)
            self.small_hand_label.pack(expand=True, padx=4, pady=4)
        except FileNotFoundError:
            self._reference_missing = True
            self.small_hand_label = ctk.CTkLabel(self.small_hand_bg, text="รูปตัวอย่าง", font=ui_font(16, "regular"), width=img_size, height=img_size)
            self.small_hand_label.pack(expand=True, padx=4, pady=4)

        self.log_button = ctk.CTkButton(
            self.right_info_container, text="ผลการฝึกของฉัน", font=self.font_btn_text, fg_color=self.purple_bg,
            text_color=self.white_fg, command=lambda: self.show_history_page(), height=self.btn_h,
            hover_color="#5B2C6F", corner_radius=15
        )
        self.log_button.place(rely=.88, relheight=.112, relwidth=1)

        self.history_page = ctk.CTkFrame(self, fg_color="#F4F7F6")
        
        self.history_body_frame = ctk.CTkFrame(self.history_page, fg_color="transparent")
        self.history_body_frame.pack(fill="both", expand=True, padx=int(15 * self.scale_w), pady=4)

        self.report_actions = ctk.CTkFrame(self.history_body_frame, fg_color="transparent")
        self.report_actions.place(relx=.795, relwidth=.205, rely=.008, relheight=.984)
        self.report_actions.pack_propagate(False)
        
        self.analysis_card = ctk.CTkFrame(self.history_body_frame, fg_color="#FFFFFF", corner_radius=22,
                                          border_width=1, border_color="#DCE4EC")
        self.analysis_card.place(relwidth=.783, rely=.008, relheight=.984)
        self.analysis_card.pack_propagate(False)
        self.report_title = ctk.CTkLabel(self.analysis_card, text="ผลการฝึกและความปวดของมือ", font=ui_font(max(26, int(30 * self.u_scale)), "bold"), text_color=self.black_fg)
        self.report_title.pack(anchor="w", padx=24, pady=(12, 0))
        self._localized_labels.append((self.report_title, "ผลการฝึก", "Practice results"))
        self.report_body = ctk.CTkFrame(self.analysis_card, fg_color="transparent")
        self.report_body.pack(fill="both", expand=True, padx=12, pady=6)
        self.gauge_column = ctk.CTkFrame(self.report_body, fg_color="transparent")
        self.gauge_column.place(relwidth=.55, relheight=1)
        self.gauge_column.pack_propagate(False)
        gauge_width = int(self.screen_width * .42) - 34
        self.gauge_size = min(440, int(self.screen_height * .50), gauge_width - 8)
        self.gauge = tk.Canvas(self.gauge_column, width=self.gauge_size, height=self.gauge_size,
                               bg="#FFFFFF", highlightthickness=0)
        self.gauge.pack(expand=True)
        self.report_progress = ctk.CTkLabel(self.gauge_column, text="ทำแล้ว 0 ท่า · 0 รอบ · 0 เซต",
                                            font=ui_font(max(22, int(26 * self.u_scale)), "semibold", max_scale=1.25), text_color=self.black_fg,
                                            wraplength=gauge_width, justify="center")
        self.report_progress.pack(pady=(0, 4))
        self.report_guidance = ctk.CTkLabel(self.gauge_column, text="เริ่มฝึกที่หน้าหลัก เมื่อทำได้แม้เพียง 1 ท่ากลับมาดูผลได้",
                                            font=ui_font(max(20, int(23 * self.u_scale)), "regular"), text_color="#52667A",
                                            wraplength=gauge_width, justify="center")
        self.report_guidance.pack(padx=6, pady=(0, 8))

        self.report_info = ctk.CTkFrame(self.report_body, fg_color="transparent")
        self.report_info.place(relx=.56, relwidth=.44, rely=.008, relheight=.984)
        report_wrap = int(self.screen_width * .32) - 36
        report_title_font = ui_font(max(21, int(26 * self.u_scale)), "semibold")
        report_value_font = ui_font(max(23, int(30 * self.u_scale)), "semibold")
        report_detail_font = ui_font(max(17, int(23 * self.u_scale)), "regular")

        self.pain_card = ctk.CTkFrame(self.report_info, fg_color="#F5EFF8",
                                        border_width=1, border_color="#DDCDE6", corner_radius=16)
        self.pain_card.place(relwidth=1, relheight=.49)
        self.pain_card_title = ctk.CTkLabel(self.pain_card, font=report_title_font, text_color="#FFFFFF",
                                          fg_color=self.purple_bg, corner_radius=9)
        self.pain_card_title.place(relx=.035, rely=.045, relwidth=.93, relheight=.20)
        self._localized_labels.append((self.pain_card_title, "ความปวดของมือ (0-10)", "Hand pain (0-10)"))
        self.report_pain_change = ctk.CTkLabel(self.pain_card, font=report_value_font,
                                               wraplength=report_wrap, justify="center")
        self.report_pain_change.place(rely=.26, relwidth=1, relheight=.22)
        self.report_pain = ctk.CTkLabel(self.pain_card, font=report_detail_font,
                                       text_color=self.black_fg, justify="center", wraplength=report_wrap)
        self.report_pain.place(relx=.03, rely=.48, relwidth=.94, relheight=.36)
        # Shown instead of the result until the after-practice pain is chosen.
        self.pain_pick = ctk.CTkFrame(self.pain_card, fg_color="transparent")
        self.pain_pick_note = ctk.CTkLabel(self.pain_pick, font=ui_font(19, "semibold", max_scale=1.3),
                                           text_color="#B83228", wraplength=report_wrap, justify="center")
        self.pain_pick_note.pack(fill="x", pady=(2, 2))
        pick_row = ctk.CTkFrame(self.pain_pick, fg_color="transparent")
        pick_row.pack(fill="x", padx=8)
        self.pain_pick_var = ctk.IntVar(value=0)
        self.pain_pick_value = ctk.CTkLabel(pick_row, text="0", width=44, font=ui_font(26, "bold", max_scale=1.3),
                                            text_color="#4A235A")
        self.pain_pick_value.pack(side="left")
        ctk.CTkSlider(pick_row, from_=0, to=10, number_of_steps=10, variable=self.pain_pick_var, height=26,
                      progress_color="#8E6BA3", button_color="#4A235A", button_hover_color="#5B2C6F",
                      command=lambda v: self.pain_pick_value.configure(
                          text=f"{int(v)}")).pack(side="left", fill="x", expand=True, padx=6)
        self.pain_pick_hint = ctk.CTkLabel(self.pain_pick, font=ui_font(16, "regular", max_scale=1.25),
                                           text_color="#52667A")
        self.pain_pick_hint.pack()
        self.pain_pick_btn = ctk.CTkButton(self.pain_pick, font=ui_font(19, "semibold", max_scale=1.3),
                                           fg_color="#4A235A", hover_color="#5B2C6F", text_color="#FFFFFF",
                                           height=max(44, int(40 * FONT_SCALE)), corner_radius=12,
                                           command=self.save_after_pain_from_report)
        self.pain_pick_btn.pack(fill="x", padx=12, pady=(4, 0))
        self._editing_after_pain = False
        self.pain_edit_btn = ctk.CTkButton(
            self.pain_card, font=ui_font(16, "semibold", max_scale=1.25), fg_color="#FFFFFF",
            text_color="#4A235A", hover_color="#F1E8F5", border_width=2, border_color="#4A235A",
            height=max(34, int(30 * FONT_SCALE)), corner_radius=10, command=self.edit_after_pain)

        self.progress_card = ctk.CTkFrame(self.report_info, fg_color="#EEF5FB",
                                         border_width=1, border_color="#CCDEED", corner_radius=16)
        self.progress_card.place(rely=.51, relwidth=1, relheight=.49)
        self.progress_title = ctk.CTkLabel(self.progress_card, font=report_title_font, text_color="#FFFFFF",
                                           fg_color="#244B72", corner_radius=9)
        self.progress_title.place(relx=.035, rely=.045, relwidth=.93, relheight=.20)
        self._localized_labels.append((self.progress_title, "ความก้าวหน้า", "Your progress"))
        self.progress_today = ctk.CTkLabel(self.progress_card, font=report_value_font,
                                           text_color="#244B72", wraplength=report_wrap)
        self.progress_today.place(rely=.28, relwidth=1, relheight=.30)
        self.progress_days = ctk.CTkLabel(self.progress_card, font=report_detail_font,
                                          text_color=self.black_fg, wraplength=report_wrap)
        self.progress_days.place(rely=.59, relwidth=1, relheight=.35)
        self.actions_title = ctk.CTkLabel(self.report_actions, text="เลือกสิ่งที่ต้องการ", font=ui_font(max(22, int(24 * self.u_scale)), "semibold"), text_color=self.black_fg)
        self.actions_title.pack(pady=(18, 12))
        self._localized_labels.append((self.actions_title, "เลือกสิ่งที่ต้องการ", "Actions"))

        self.export_button = ctk.CTkButton(
            self.report_actions, text="ส่งออกเป็นเว็บ", font=self.font_btn_text,
            fg_color="#137A4B", text_color="#FFFFFF", hover_color="#0C5F39",
            command=self.export_completed_sets, height=max(68, int(105 * self.scale_h)), corner_radius=14)
        self.export_button.pack(side="top", fill="x", padx=8, pady=10)
        self.export_note = ctk.CTkLabel(self.report_actions, text="สแกน QR ดูผลบนมือถือ", font=ui_font(18, "regular", max_scale=1.25), text_color="#43566A")
        self.export_note.pack(pady=(0, 4))
        self._localized_labels.append((self.export_note, "สแกน QR ดูผลบนมือถือ", "Scan QR on a phone"))

        self.report_reset_button = ctk.CTkButton(
            self.report_actions, text="รีเซ็ตผลการฝึก", font=self.font_btn_text,
            fg_color="#B83228", text_color="#FFFFFF", hover_color="#8C251E",
            command=self.reset_action, height=max(68, int(105 * self.scale_h)), corner_radius=14)
        self.report_reset_button.pack(side="top", fill="x", padx=8, pady=10)

        self.next_advice_button = ctk.CTkButton(
            self.report_actions, text="คำแนะนำครั้งถัดไป", font=self.font_btn_text,
            fg_color="#244B72", text_color="#FFFFFF", hover_color="#183854",
            command=self.show_next_advice, height=max(68, int(105 * self.scale_h)), corner_radius=14)
        self.next_advice_button.pack(side="top", fill="x", padx=8, pady=10)

        self.back_button = ctk.CTkButton(
            self.report_actions, text="กลับหน้าหลัก", font=self.font_btn_text, fg_color="#E8A126",
            text_color="#1F2937", hover_color="#D48C11", command=self.show_main_page,
            height=max(68, int(105 * self.scale_h)), corner_radius=14
        )
        self.back_button.pack(side="bottom", fill="x", padx=8, pady=8)

        
        self.pose_sounds = {1: ["001.mp3"], 2: ["002.mp3"], 3: ["003.mp3"], 4: ["004.mp3"], 5: ["005.mp3"]}

        self.running = False
        self.countdown_active = False
        self.countdown_job = None
        self.countdown_total = 0
        self.countdown_end_time = 0

        self.goal_popup = ctk.CTkFrame(self, fg_color="#FCF3CF", corner_radius=15, border_width=2, border_color="#F1C40F")
        self.goal_popup_label = ctk.CTkLabel(
            self.goal_popup, text="สุดยอดมาก!\nคุณทำครบเป้าหมายที่ตั้งไว้แล้ว!", 
            font=ui_font(int(26 * self.u_scale), "semibold"), text_color="#B7950B", justify="center"
        )
        self.goal_popup_label.pack(padx=25, pady=20)

        self.config_popup = ctk.CTkFrame(self, fg_color="#FFFFFF", corner_radius=22, border_width=3,
                                         border_color=self.purple_bg)
        self.config_popup_title = ctk.CTkLabel(self.config_popup, font=ui_font(24, "bold"), text_color=self.purple_bg)
        self.config_popup_title.pack(padx=28, pady=(20, 0))
        self.config_popup_note = ctk.CTkLabel(self.config_popup, font=ui_font(18, "regular"), text_color="#52667A")
        self.config_popup_note.pack(padx=28, pady=(0, 12))
        self._localized_labels.append((self.config_popup_note, "AI จะนับเฉพาะมือข้างที่เลือก",
                                       "Only the selected hand is counted"))
        row = ctk.CTkFrame(self.config_popup, fg_color="transparent")
        row.pack(padx=24)
        self.hand_buttons = {}
        for column, hand in enumerate(("ซ้าย", "ขวา")):
            self.hand_buttons[hand] = ctk.CTkButton(
                row, font=ui_font(24, "bold"), width=max(170, int(self.screen_width * .14)),
                height=max(80, int(64 * FONT_SCALE)), corner_radius=16, border_width=3,
                border_color=self.purple_bg, command=lambda h=hand: self.select_hand(h))
            self.hand_buttons[hand].grid(row=0, column=column, padx=8)
        self.config_close_btn = ctk.CTkButton(
            self.config_popup, text="ปิด", font=ui_font(20, "semibold"), fg_color="#EEF1F4", text_color=self.black_fg,
            hover_color="#DCE3EA", height=48, width=160, corner_radius=12, command=self.close_config_popup)
        self.config_close_btn.pack(pady=(16, 20))

        self.update_idletasks()
        self.attributes("-fullscreen", True)
        self.after(50, self._reveal)

        self.refresh_language()
        voice_worker = threading.Thread(target=self._voice_loop, name="voice", daemon=True)
        self._workers.append(voice_worker)
        voice_worker.start()
        self.check_sensor_loop()
        self.protocol("WM_DELETE_WINDOW", self.on_close)
        self._video_job = self.after(0, self._start_video)

    def _show_splash(self):
        try:
            splash = tk.Toplevel(self, bg="#4A235A")
            splash.geometry(f"{self.winfo_screenwidth()}x{self.winfo_screenheight()}+0+0")
            splash.attributes("-fullscreen", True)
            from tkinter import font as tkfont
            family = "Prompt TH" if "Prompt TH" in tkfont.families(self) else "Sarabun"
            tk.Label(splash, text="เครื่องบริหารนิ้วมืออัจฉริยะ", bg="#4A235A", fg="#FFFFFF",
                     font=(family, 34, "bold")).place(relx=.5, rely=.45, anchor="center")
            tk.Label(splash, text="กำลังเปิดโปรแกรม...", bg="#4A235A", fg="#D9C8E3",
                     font=(family, 22)).place(relx=.5, rely=.56, anchor="center")
            splash.update()
            return splash
        except Exception:
            logging.exception("Splash screen failed")
            return None

    def _reveal(self):
        self.geometry(f"{self.screen_width}x{self.screen_height}+0+0")
        self.deiconify()
        self.attributes("-fullscreen", True)
        self.lift()
        if self._splash is not None:
            self.after(150, self._splash.destroy)
            self._splash = None

    def show_dialog(self, title, message, kind="info", yes=None, no=None):
        """Large, high-contrast dialog for older users (replaces small messageboxes).

        kind: info / warning / error / question. With `no` given it asks and
        returns True for `yes`, False otherwise.
        """
        colors = {"info": "#244B72", "warning": "#A56A00", "error": "#B83228", "question": "#4A235A"}
        icons = {"info": "i", "warning": "!", "error": "!", "question": "?"}
        color = colors.get(kind, "#244B72")
        result = {"value": False}
        dialog = ctk.CTkToplevel(self)
        dialog.title(title)
        dialog.configure(fg_color="#FFFFFF")
        dialog.overrideredirect(True)  # no small title bar: the dialog draws its own title
        dialog.transient(self)
        width = min(1000, max(600, int(self.screen_width * .72)))
        wrap = width - 80
        frame = ctk.CTkFrame(dialog, fg_color="#FFFFFF", border_width=6, border_color=color, corner_radius=0)
        frame.pack(fill="both", expand=True)
        ctk.CTkLabel(frame, text=icons.get(kind, "i"), width=110, height=110, corner_radius=55, fg_color=color,
                     text_color="#FFFFFF", font=ui_font(56, "bold", max_scale=1.2)).pack(pady=(34, 12))
        ctk.CTkLabel(frame, text=title, font=ui_font(36, "bold", max_scale=1.3), text_color=color,
                     wraplength=wrap, justify="center").pack(padx=30)
        ctk.CTkLabel(frame, text=message, font=ui_font(28, "regular", max_scale=1.3), text_color=self.black_fg,
                     wraplength=wrap, justify="center").pack(padx=30, pady=(12, 28))
        row = ctk.CTkFrame(frame, fg_color="transparent")
        row.pack(pady=(0, 34))

        def close(value):
            result["value"] = value
            dialog.destroy()
        button = dict(font=ui_font(28, "bold", max_scale=1.3), height=max(72, int(58 * FONT_SCALE)),
                      width=max(200, int(width * .32)), corner_radius=16)
        if no is not None:
            ctk.CTkButton(row, text=no, fg_color="#EEF1F4", hover_color="#DCE3EA", text_color=self.black_fg,
                          command=lambda: close(False), **button).pack(side="left", padx=10)
        ctk.CTkButton(row, text=yes or ui("ตกลง", "OK"), fg_color=color, hover_color=self.purple_bg,
                      text_color="#FFFFFF", command=lambda: close(True), **button).pack(side="left", padx=10)
        dialog.bind("<Escape>", lambda e: close(False))
        dialog.update_idletasks()
        height = dialog.winfo_reqheight()
        dialog.geometry(f"{width}x{height}+{(self.screen_width-width)//2}+{max(0, (self.screen_height-height)//2)}")
        dialog.resizable(False, False)
        dialog.lift()
        try:
            dialog.wait_visibility()
            dialog.grab_set()
        except tk.TclError:
            pass
        dialog.focus_force()
        self.wait_window(dialog)
        return result["value"]

    def set_feedback(self, thai, english, color):
        self._last_feedback = (thai, english, color)
        self.pose_feedback_label.configure(text=ui(thai, english), text_color=color)

    def set_breathing(self, thai, english, color):
        self._last_breathing = (thai, english, color)
        self.breathing_label.configure(text=ui(thai, english), text_color=color)

    def toggle_language(self):
        global UI_LANGUAGE
        UI_LANGUAGE = "en" if UI_LANGUAGE == "th" else "th"
        self._queue_voice(None)
        self.refresh_language()
        self._web_server.set_language(UI_LANGUAGE)
        if UI_LANGUAGE == "en" and not self._voice_warning_shown and not shutil.which("mpg123"):
            self._voice_warning_shown = True
            self.show_dialog("Voice unavailable", "On the Pi, install the audio player:\nsudo apt install mpg123", "warning")
        elif UI_LANGUAGE == "en":
            if self.running and self.main_content_frame.winfo_ismapped():
                self._queue_voice(self.pose_sounds[self.current_pose][0])
            else:
                self._queue_voice("017.mp3")
        if getattr(self, "advice_popup", None) is not None and self.advice_popup.winfo_exists():
            self.advice_popup.destroy()
            self.show_next_advice()

    def refresh_language(self):
        self.title(ui("เครื่องบริหารนิ้วมืออัจฉริยะ", "Finger Exercise Coach"))
        self.app_title_label.configure(text=ui("เครื่องบริหารนิ้วมืออัจฉริยะ", "Finger Exercise Coach"))
        if self.logo_label.cget("text"):
            self.logo_label.configure(text=ui("ตราสัญลักษณ์", "LOGO"))
        self.language_button.configure(text=ui("English", "ไทย"))
        self.match_badge.configure(text=ui("กำลังหามือ", "Looking for hand"))
        self.env_badge.configure(text=ui("AI: กำลังเริ่มต้น...", "AI: starting..."))
        with self.frame_lock:
            self.latest_env_text = ui("AI: กำลังติดตาม...", "AI: tracking...")
        for label, thai, english in self._localized_labels:
            label.configure(text=ui(thai, english))
        self.update_text()
        self.btn_select_hand.configure(text=ui(
            f"มือ{self.target_hand_var.get()} ▾",
            f"{hand_label(self.target_hand_var.get())} hand ▾"))
        self.pain_btn.configure(text=ui("บันทึกแล้ว", "Saved") if self._pain_button_saved
                                else ui("บันทึก", "Save"))
        self.start_stop_button.configure(text=ui("หยุด", "Pause") if self.running or self.countdown_active
                                         else self._start_label())
        self.reset_button.configure(text=ui("รีเซ็ต", "Reset"))
        self.log_button.configure(text=ui("ผลการฝึกของฉัน", "My results"))
        self.export_button.configure(text=ui("ส่งออกเป็นเว็บ", "Web report"))
        self.report_reset_button.configure(text=ui("รีเซ็ตผลการฝึก", "Reset results"))
        self.next_advice_button.configure(text=ui("คำแนะนำ", "Practice tips"))
        self.back_button.configure(text=ui("กลับหน้าหลัก", "Home"))
        self.config_popup_title.configure(text=ui("เลือกมือที่ต้องการฝึก", "Choose a hand"))
        self.goal_popup_label.configure(text=ui("สุดยอดมาก!\nคุณทำครบเป้าหมายที่ตั้งไว้แล้ว!",
                                                "Well done!\nYou finished your practice goal!"))
        self.set_feedback(*self._last_feedback)
        self.set_breathing(*self._last_breathing)
        if self._reference_missing:
            self.small_hand_label.configure(text=ui("รูปตัวอย่าง", "Example pose"))
        if self.config_popup.winfo_ismapped():
            self.open_hand_popup()
        self.update_round()
        self.update_live_report()

    def show_config_popup(self):
        self.config_popup.place(relx=0.5, rely=0.5, anchor="center")
        self.config_popup.tkraise()

    def close_config_popup(self):
        self.config_popup.place_forget()

    def open_hand_popup(self):
        # Widgets are created once; opening only recolours them (fast, no flicker).
        self.config_popup_title.configure(text=ui("เลือกมือที่ต้องการฝึก", "Choose a hand"))
        self.config_close_btn.configure(text=ui("ปิด", "Close"))
        for hand, button in self.hand_buttons.items():
            chosen = self.target_hand_var.get() == hand
            # Hover colour always contrasts with the text, so the label never disappears.
            button.configure(text=ui(f"มือ{hand}", f"{hand_label(hand)} hand"),
                             fg_color=self.purple_bg if chosen else "#FFFFFF",
                             hover_color="#5B2C6F" if chosen else "#F1E8F5",
                             text_color="#FFFFFF" if chosen else self.purple_bg)
        self.show_config_popup()

    def select_hand(self, val):
        if val not in ("ซ้าย", "ขวา"):
            raise ValueError("เลือกได้เฉพาะมือซ้ายหรือมือขวา")
        self.target_hand_var.set(val)
        self._match_gate.reset()
        self._presence_latch.last_seen = float('-inf')
        self.set_hand_posit_state(False)
        self.btn_select_hand.configure(text=ui(f"มือ{val} ▾",
                                               f"{hand_label(val)} hand ▾"))
        self.close_config_popup()
        if UI_LANGUAGE == "en":
            self._queue_voice("015.mp3" if val == "ซ้าย" else "016.mp3")

    def trigger_goal_popup(self, finished_set):
        msg = ui(f"จบเซตที่ {finished_set} แล้ว!\nพักมือ 1–2 นาที แล้วกด \"เริ่มเซตถัดไป\"\nหรือดูผลที่ \"ผลการฝึกของฉัน\"",
                 f"Set {finished_set} complete!\nRest 1–2 minutes, then tap Next set\nor open My results.")
        self.goal_popup_label.configure(text=msg)
        self.goal_popup.place(relx=0.5, rely=0.5, anchor="center")
        self.goal_popup.tkraise()
        self.after(5000, self.goal_popup.place_forget)

    def save_pain_log(self):
        val = self.pain_var.get()
        self._last_pain = val
        # Home page = pain BEFORE practice only. "After" is chosen on the report page.
        self._pain_before = val
        when = ui("ก่อนฝึก", "before")
        self.write_log(f"PainBefore: {val}")
        if self.history_page.winfo_ismapped():
            self.update_live_report()
        self._save_report_state()
        self._pain_button_saved = True
        # Make the save obvious: green button, green card and the saved value in the title.
        # A solid green banner covers the whole pain card for 2.5 s: easy to see from a distance.
        self.pain_saved_banner.configure(text=ui(f"บันทึกแล้ว\n{when} {val}/10 · {pain_description(val)}",
                                                 f"Saved: {val}/10\n{pain_description(val)}"))
        self.pain_saved_banner.place(relx=0, rely=0, relwidth=1, relheight=1)
        self.pain_saved_banner.lift()
        if getattr(self, "_pain_reset_job", None):
            self.after_cancel(self._pain_reset_job)
        self._pain_reset_job = self.after(2500, self.reset_pain_button)
        if UI_LANGUAGE == "en":
            self._queue_voice("012.mp3")

    def edit_after_pain(self):
        self._editing_after_pain = True
        self.update_live_report()

    def save_after_pain_from_report(self):
        self._editing_after_pain = False
        val = int(self.pain_pick_var.get())
        self._pain_after = self._last_pain = val
        self.write_log(f"PainAfter: {val}")
        self._save_report_state()
        self.update_live_report()
        if UI_LANGUAGE == "en":
            self._queue_voice("012.mp3")

    def reset_pain_button(self):
        self._pain_button_saved = False
        self._pain_reset_job = None
        self.pain_saved_banner.place_forget()
        self.pain_btn.configure(text=ui("บันทึก", "Save"))

    def _report_state_path(self):
        return os.path.join(os.path.dirname(os.path.abspath(__file__)), "report_state.json")

    def _load_report_state(self):
        try:
            with open(self._report_state_path(), "r", encoding="utf-8") as source:
                state = json.load(source)
            started = datetime.fromisoformat(state["started_at"])
            if started.tzinfo is None:
                raise ValueError("Report timestamp lacks time zone")
            if datetime.now().astimezone() - started >= timedelta(days=5):
                self._clear_report_storage()
                return
            records = state.get("completed_sets", [])
            if isinstance(records, list):
                self._report_started_at = started
                self.completed_sets = [item for item in records if isinstance(item, dict)
                                       and item.get("total_poses") == 15]
            for name in ("pain_before", "pain_after"):
                value = state.get(name)
                if type(value) is int and 0 <= value <= 10:
                    setattr(self, "_" + name, value)
            self._last_pain = self._pain_after if self._pain_after is not None else self._pain_before
            progress = state.get("progress") or {}
            if (type(progress.get("round")) is int and 0 <= progress["round"] <= 2
                    and type(progress.get("pose")) is int and 1 <= progress["pose"] <= 5):
                self._saved_progress = progress
        except FileNotFoundError:
            # A report log without a state file has no reliable five-day start.
            self._clear_report_storage()
        except (OSError, ValueError, KeyError, TypeError, json.JSONDecodeError) as exc:
            logging.info("Starting new report: %s", exc)
            self._clear_report_storage()

    def _clear_report_storage(self):
        base = os.path.dirname(os.path.abspath(__file__))
        for name in ("Anti-Finger.txt", "Anti-Finger.txt.tmp", "report_state.json", "report_state.json.tmp"):
            path = os.path.join(base, name)
            try:
                os.remove(path)
            except FileNotFoundError:
                pass
            except OSError:
                logging.exception("Cannot clear report file: %s", path)

    def _save_report_state(self):
        path = self._report_state_path()
        temporary = path + ".tmp"
        try:
            with open(temporary, "w", encoding="utf-8") as output:
                json.dump({"started_at": self._report_started_at.isoformat(timespec="seconds"),
                           "completed_sets": self.completed_sets,
                           "progress": {"round": getattr(self, "round", 0),
                                        "pose": getattr(self, "current_pose", 1),
                                        "stable_poses": getattr(self, "_set_stable_poses", 0),
                                        "hand": self.target_hand_var.get()},
                           "pain_before": self._pain_before,
                           "pain_after": self._pain_after}, output, ensure_ascii=False, indent=2)
            os.replace(temporary, path)
        except OSError:
            logging.exception("Cannot save report state")

    def _prune_activity_log(self):
        path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "Anti-Finger.txt")
        if not os.path.exists(path):
            return
        cutoff = datetime.now() - timedelta(days=5)
        try:
            with open(path, "r", encoding="utf-8") as source:
                lines = source.readlines()
            recent = []
            for line in lines:
                try:
                    timestamp = datetime.strptime(line[1:20], "%Y-%m-%d %H:%M:%S")
                except ValueError:
                    continue
                if timestamp >= cutoff:
                    recent.append(line)
            temporary = path + ".tmp"
            with open(temporary, "w", encoding="utf-8") as output:
                output.writelines(recent)
            os.replace(temporary, path)
        except OSError:
            logging.exception("Cannot prune old activity log")

    def _expire_report_if_needed(self):
        if datetime.now().astimezone() - self._report_started_at < timedelta(days=5):
            return
        self.reset_action(confirm=False)

    def update_live_report(self):
        partial = self.round * 5 + self.current_pose - 1
        done = self.set * 15 + partial
        if done == 0:
            status, color = ui("พร้อมเริ่มฝึก", "Ready to begin"), "#8191A1"
            guidance = ui("เริ่มฝึกที่หน้าหลัก เมื่อทำได้แม้เพียง 1 ท่ากลับมาดูผลได้",
                          "Tap Start on the home screen.")
        elif partial == 0:
            status, color = ui(f"ครบ {self.set} เซต", f"{self.set} {'set' if self.set == 1 else 'sets'} done"), "#137A4B"
            guidance = ui("พักมือก่อน แล้วเริ่มเซตถัดไปได้", "Rest, then start another set if you like.")
        else:
            status, color = ui("กำลังฝึก", "In progress"), "#A56A00"
            guidance = ui(f"เซตที่ {self.set + 1} ทำแล้ว {partial}/15 ท่า · บันทึกไว้แล้ว",
                          f"Set {self.set + 1}: {partial}/15 poses saved")
        size = self.gauge_size
        pad = max(14, size // 14)
        width = max(13, size // 15)
        self.gauge.delete("all")
        self.gauge.create_oval(pad, pad, size-pad, size-pad, outline=color, width=width)
        self.gauge.create_text(size/2, size*.43, text=status, fill=color,
                               font=ui_font(max(18, int(size*.068)), "semibold", max_scale=1.0), width=size*.77)
        self.gauge.create_text(size/2, size*.61, text=ui(f"{done} ท่า", f"{done} poses"), fill=self.black_fg,
                               font=ui_font(max(28, int(size*.105)), "bold", max_scale=1.0))
        self.report_progress.configure(text=ui(
            f"ทำแล้วทั้งหมด {done} ท่า\nครบ {self.set} เซต · รอบนี้ {self.round}/3",
            f"{done} poses in total\n{self.set} {'set' if self.set == 1 else 'sets'} done · round {self.round}/3"))
        self.report_guidance.configure(text=guidance)
        pain_text, pain_color, advice = pain_advice(self._pain_before, self._pain_after)
        self.report_pain_change.configure(text=pain_text, text_color=pain_color)
        self.report_pain.configure(text=advice)
        # Report page = pain AFTER practice. Until it is chosen (or while editing) the
        # card shows a picker; afterwards the before/after comparison and an edit button.
        if done > 0 and (self._pain_after is None or self._editing_after_pain):
            mode = "pick"
        elif done > 0 and self._pain_after is not None:
            mode = "result"
        else:
            mode = "idle"
        self.pain_pick_note.configure(text=ui("เลือกระดับความปวดหลังฝึก เพื่อดูผล",
                                              "Choose your pain after practice to see the result"))
        self.pain_pick_hint.configure(text=ui("0 = ไม่ปวด · 10 = ปวดมากที่สุด", "0 = no pain · 10 = worst"))
        self.pain_pick_btn.configure(text=ui("บันทึกและดูผล", "Save and show result"))
        self.pain_edit_btn.configure(text=ui("แก้ไขความปวดหลังฝึก", "Change pain after practice"))
        if mode != getattr(self, "_pain_layout", None):
            self._pain_layout = mode
            for widget in (self.pain_pick, self.report_pain_change, self.report_pain, self.pain_edit_btn):
                widget.place_forget()
            if mode == "idle":
                self.pain_card.place_configure(relheight=.49)
                self.progress_card.place_configure(rely=.51, relheight=.49)
                self.pain_card_title.place_configure(rely=.045, relheight=.20)
                self.report_pain_change.place(rely=.26, relwidth=1, relheight=.22)
                self.report_pain.place(relx=.03, rely=.48, relwidth=.94, relheight=.50)
            else:
                # Taller pain card: the picker or the result plus edit button need room.
                self.pain_card.place_configure(relheight=.63)
                self.progress_card.place_configure(rely=.65, relheight=.35)
                self.pain_card_title.place_configure(rely=.03, relheight=.14)
                if mode == "pick":
                    start = (self._pain_after if self._pain_after is not None
                             else self._pain_before if self._pain_before is not None else 0)
                    self.pain_pick_var.set(start)
                    self.pain_pick_value.configure(text=str(start))
                    self.pain_pick.place(relx=.03, rely=.19, relwidth=.94, relheight=.79)
                else:
                    self.report_pain_change.place(rely=.18, relwidth=1, relheight=.15)
                    self.report_pain.place(relx=.03, rely=.33, relwidth=.94, relheight=.48)
                    self.pain_edit_btn.place(relx=.5, rely=.83, anchor="n", relwidth=.7)
        self.draw_five_day_trend()

    def draw_five_day_trend(self):
        now = time.time()
        if now - self._daily_pose_cache_time > 10 or not self._daily_pose_counts:
            days = [(datetime.now().date() - timedelta(days=offset)) for offset in range(4, -1, -1)]
            counts = {day: 0 for day in days}
            path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "Anti-Finger.txt")
            try:
                with open(path, "r", encoding="utf-8") as source:
                    for line in source:
                        if "ท่า " not in line or "สำเร็จ" not in line:
                            continue
                        try:
                            day = datetime.strptime(line[1:11], "%Y-%m-%d").date()
                        except ValueError:
                            continue
                        if day in counts:
                            counts[day] += 1
            except (OSError, UnicodeError):
                pass
            self._daily_pose_counts = [(day, counts[day]) for day in days]
            self._daily_pose_cache_time = now
        today = self._daily_pose_counts[-1][1]
        active_days = sum(count > 0 for _, count in self._daily_pose_counts)
        self.progress_today.configure(text=ui(
            f"วันนี้ {today} ท่า",
            f"Today: {today} {'pose' if today == 1 else 'poses'}"))
        self.progress_days.configure(text=ui(f"ฝึกแล้ว {active_days} วันใน 5 วันล่าสุด",
                                              f"Days practiced: {active_days} of 5"))

    def update_set_analysis(self):
        self.update_live_report()

    POSE_CUES = {
        1: ("เหยียดนิ้วทุกนิ้วให้ตรงที่สุดเท่าที่ทำได้ ข้อมือตรง ไม่แอ่นหรืองอ",
            "Straighten all fingers as far as is comfortable; keep the wrist straight."),
        2: ("งอเฉพาะข้อกลางและข้อปลายนิ้ว ให้โคนนิ้วตรง มือเป็นรูปตะขอ",
            "Bend only the middle and end finger joints; keep the knuckles straight (hook)."),
        3: ("กำมือเบา ๆ ให้ปลายนิ้วแตะฝ่ามือ ไม่ต้องบีบแรง",
            "Make a gentle fist with fingertips touching the palm; don't squeeze."),
        4: ("งอโคนนิ้วและข้อกลาง ให้ปลายนิ้วแตะโคนฝ่ามือ ข้อปลายนิ้วตรง",
            "Bend the knuckles and middle joints so the fingertips touch the base of the palm."),
        5: ("งอที่โคนนิ้วประมาณมุมฉาก นิ้วที่เหลือเหยียดตรงเหมือนโต๊ะ",
            "Bend at the knuckles to about a right angle with the fingers straight, like a tabletop."),
    }

    def _practice_tips(self):
        """Advice in three parts, the way a physiotherapist would brief a patient:
        what to do now, care after practice, and when (and whom) to see.

        Based on usual tendon-gliding home programmes and the pain-monitoring
        rule used in the pain card. General guidance, not a diagnosis.
        """
        partial = self.round * 5 + self.current_pose - 1
        before, after = self._pain_before, self._pain_after
        latest = after if after is not None else before
        rising = before is not None and after is not None and after - before >= 2

        # 1) Right now
        if latest is not None and latest >= 7:
            now_title, now_color = ui("ตอนนี้: ควรหยุดฝึก", "Now: stop for today"), "#B83228"
            now = [ui("ระดับปวด 7 ขึ้นไป หยุดฝึกวันนี้ พักมือ และอย่ากำหรือบีบของแรง ๆ",
                      "Pain is 7 or more: stop today, rest the hand and avoid gripping or squeezing."),
                   ui("ถ้าพรุ่งนี้ยังปวดระดับนี้ ให้ปรึกษาแพทย์หรือนักกายภาพบำบัดก่อนฝึกต่อ",
                      "If it is still this painful tomorrow, see a doctor or physiotherapist before practising again.")]
        elif partial == 0 and self.set == 0:
            now_title, now_color = ui("ก่อนเริ่มฝึก", "Before you start"), "#244B72"
            now = [ui("นั่งหลังตรง วางศอกบนโต๊ะ ให้มือทั้งมืออยู่กลางภาพกล้อง",
                      "Sit upright, elbow on the table, whole hand in the middle of the camera view."),
                   ui("ถ้านิ้วตึงตอนเช้า แช่มือในน้ำอุ่น 5–10 นาทีก่อนฝึก จะขยับได้ง่ายขึ้น",
                      "If fingers are stiff in the morning, soak the hand in warm water for 5–10 minutes first."),
                   ui("ทำช้า ๆ ค้างท่าละ 5 วินาที หายใจตามปกติ ตึงหรือปวดเล็กน้อย (0–3) ทำต่อได้",
                      "Move slowly, hold each pose 5 seconds, keep breathing. Mild tightness (0–3) is fine.")]
            if before is None:
                now.append(ui("บันทึกระดับปวดก่อนเริ่ม เพื่อใช้เทียบผลหลังฝึก",
                              "Record your pain first so you can compare after practice."))
        elif partial:
            left = 6 - self.current_pose
            now_title, now_color = ui(f"เซตที่ {self.set + 1} · รอบที่ {self.round + 1}/3 · รอบนี้เหลือ {left} ท่า",
                                      f"Set {self.set + 1} · round {self.round + 1}/3 · {left} left this round"), "#A56A00"
            thai, english = self.POSE_CUES[self.current_pose]
            now = [ui(f"ท่าที่ {self.current_pose}: {thai}", f"Pose {self.current_pose}: {english}")]
            if self._pose_had_long_pause or self._set_stable_poses < partial:
                now.append(ui("ถ้าเวลาหยุดนับบ่อย เลื่อนมือเข้ากลางภาพ หันหน้าเข้าหาแสง และค้างท่าให้นิ่ง",
                              "If the timer keeps pausing, centre the hand, face the light and hold still."))
            now.append(ui("ปวดเกินระดับ 3 หรือเจ็บแปลบ ชา ให้หยุดพักทันที",
                          "Stop and rest if pain goes above 3 or you feel sharp pain or numbness."))
        else:
            last = self.completed_sets[-1]["stable_poses"] if self.completed_sets else 0
            now_title, now_color = ui(f"ทำครบ {self.set} เซตแล้ว", f"{self.set} {'set' if self.set == 1 else 'sets'} done"), "#137A4B"
            now = [ui(f"เซตล่าสุดกล้องนับต่อเนื่อง {last}/15 ท่า" + (" คงจังหวะนี้ไว้" if last >= 12 else
                      " ครั้งหน้าค้างท่าให้นิ่งในกรอบกล้องจนเวลาครบ"),
                      f"Last set: {last}/15 steady poses." + (" Keep this pace." if last >= 12 else
                      " Next time hold still in view until the timer ends."))]
            if latest is not None and (latest >= 4 or rising):
                now.append(ui("ไม่ควรเพิ่มเซตวันนี้ เพราะความปวดสูงหรือเพิ่มขึ้นหลังฝึก",
                              "Don't add more sets today: pain is high or went up after practice."))
            else:
                now.append(ui("ถ้ามือยังสบาย พัก 1–2 นาทีแล้วเริ่มเซตถัดไปได้ ครั้งหนึ่งไม่ควรเกิน 3 เซต",
                              "If the hand feels fine, rest 1–2 minutes before another set; no more than 3 sets per session."))
            now.append(ui("ฝึกสม่ำเสมอวันละ 2–3 ครั้ง หรือตามที่นักกายภาพบำบัดกำหนด ได้ผลดีกว่าฝึกหนักครั้งเดียว",
                          "Practise 2–3 times a day, or as your physiotherapist advises; regular beats one long session."))
            if after is None:
                now.append(ui("บันทึกระดับปวดหลังฝึกที่หน้าหลัก เพื่อดูว่าการฝึกเหมาะกับมือหรือไม่",
                              "Record your pain after practice to check the exercise suits you."))

        # 2) After practice / at home
        care = [ui("หลังฝึก กำ–แบมือเบา ๆ 5–10 ครั้ง แล้วปล่อยมือให้คลาย",
                   "Open and close the hand gently 5–10 times, then relax."),
                ui("ถ้ามือตึงหรือปวดเล็กน้อย ประคบอุ่น 10–15 นาที ถ้าบวมหรือปวดหลังฝึก ประคบเย็น (ห่อผ้า) 10–15 นาที",
                   "Stiff: warm pack 10–15 min. Swollen or sore: wrapped cold pack 10–15 min."),
                ui("ช่วงที่ยังปวด เลี่ยงการกำหรือบีบแรงซ้ำ ๆ เช่น บิดผ้า หิ้วถุงหนัก ใช้กรรไกรหรือเครื่องมือนาน ๆ",
                   "While it hurts, avoid hard gripping: wringing cloths, heavy bags, tools."),
                ui("ปวดหลังฝึกควรลดลงภายในวันเดียวกัน ถ้ายังปวดถึงเช้าวันรุ่งขึ้น ให้ลดจำนวนรอบหรือเวลาค้างท่าลงครึ่งหนึ่ง",
                   "Soreness should settle the same day; if not, do half as much next time.")]

        # 3) When and whom to see
        see = [ui("ไปโรงพยาบาลทันที ถ้านิ้วบวมแดงร้อนทั้งนิ้ว ปวดมากเวลาเหยียด มีไข้ หรือนิ้วชา ซีด เย็น",
                  "Hospital now: finger red, hot and swollen, fever, or numb and cold."),
               ui("พบแพทย์ภายใน 1–2 วัน ถ้านิ้วล็อกงออยู่แล้วเหยียดเองไม่ได้ หรือปวดมากขึ้นทุกวัน",
                  "Doctor within 1–2 days: finger locked bent, or pain worse every day."),
               ui("ปรึกษานักกายภาพบำบัดภายใน 1 สัปดาห์ ถ้าปวดหลังฝึกไม่หายใน 24 ชม. ติดกันหลายวัน หรือปวดตอนกลางคืน",
                  "Physiotherapist within a week: soreness over 24 h for days, or pain at night."),
               ui("ถ้าฝึกต่อเนื่อง 4–6 สัปดาห์แล้วนิ้วยังสะดุดหรือล็อก ควรพบแพทย์ออร์โธปิดิกส์ (กระดูกและข้อ) หรือแพทย์เวชศาสตร์ฟื้นฟู",
                  "Still catching after 4–6 weeks: see a bone and joint or rehab doctor.")]
        if latest is not None and latest >= 4:
            see.insert(0, ui(f"ระดับปวดล่าสุด {latest}/10 ถ้าไม่ลดลงภายใน 24 ชม. ควรปรึกษานักกายภาพบำบัด",
                             f"Pain {latest}/10: no better in 24 h? See a physiotherapist."))
        return [(now_title, now_color, "#F5EFF8", now),
                (ui("ดูแลมือหลังฝึก", "Care after practice"), "#244B72", "#EEF5FB", care),
                (ui("เมื่อไหร่ควรไปพบแพทย์", "When to get help"), "#B83228", "#FDECEA", see)]

    def short_advice(self):
        """Three short steps plus three "see a doctor" rules: easy for older readers."""
        done = self.set * 15 + self.round * 5 + self.current_pose - 1
        before, after = self._pain_before, self._pain_after
        latest = after if after is not None else before
        if latest is not None and (latest >= 7 or (before is not None and after is not None and after - before >= 2)):
            todo = [ui("วันนี้หยุดฝึก พักมือก่อน", "Stop for today and rest"),
                    ui("ประคบเย็น (ห่อผ้า) 10 นาที", "Cold pack (wrapped) for 10 minutes"),
                    ui("พรุ่งนี้ยังปวด ปรึกษานักกายภาพ", "Still sore tomorrow? Ask a physiotherapist")]
        elif latest is not None and latest >= 4:
            todo = [ui("ฝึกเบาลง ทำช้า ๆ", "Go gentler and slower"),
                    ui("พักระหว่างรอบได้", "Rest between rounds"),
                    ui("ไม่ดีขึ้นใน 1 วัน ปรึกษานักกายภาพ", "No better in a day? Ask a physiotherapist")]
        elif done == 0:
            todo = [ui("นั่งตรง วางมือกลางกล้อง", "Sit up, hand in the middle of the camera"),
                    ui("ค้างท่าละ 5 วินาที", "Hold each pose for 5 seconds"),
                    ui("เจ็บแปลบ ให้หยุดทันที", "Stop at once if it hurts sharply")]
        else:
            todo = [ui("ฝึกต่อ วันละ 2–3 ครั้ง", "Keep going, 2–3 times a day"),
                    ui("หลังฝึก ประคบอุ่น 10 นาที", "Warm pack for 10 minutes after practice"),
                    ui("ถ้าปวดมาก ให้หยุดพัก", "Rest if it hurts a lot")]
        doctor = [(ui("นิ้วบวม แดง ร้อน มีไข้", "Finger swollen, red, hot or fever"),
                   ui("ไปโรงพยาบาลทันที", "Go to hospital now")),
                  (ui("นิ้วล็อก เหยียดไม่ออก", "Finger locked, can't straighten"),
                   ui("พบแพทย์ใน 1–2 วัน", "See a doctor within 1–2 days")),
                  (ui("ฝึก 6 สัปดาห์แล้วไม่ดีขึ้น", "No better after 6 weeks"),
                   ui("พบแพทย์กระดูกและข้อ", "See a bone and joint doctor"))]
        return todo, doctor

    def show_next_advice(self):
        if getattr(self, "advice_popup", None) is not None and self.advice_popup.winfo_exists():
            self.advice_popup.destroy()
        sections = self._practice_tips()
        popup = ctk.CTkToplevel(self)
        self.advice_popup = popup
        popup.title(ui("คำแนะนำครั้งถัดไป", "Practice tips"))
        popup.configure(fg_color="#FFFFFF")
        width = min(980, max(560, int(self.screen_width * .80)))
        height = int(self.screen_height * .95)
        popup.resizable(False, False)
        popup.transient(self)
        popup.geometry(f"{width}x{height}+{(self.screen_width-width)//2}+{(self.screen_height-height)//2}")
        ctk.CTkLabel(popup, text=ui("คำแนะนำครั้งถัดไป", "Practice tips"), font=ui_font(28, "bold"),
                     text_color=self.purple_bg).pack(pady=(14, 4))
        ctk.CTkButton(popup, text=ui("เข้าใจแล้ว", "OK"), font=ui_font(24, "semibold"),
                      fg_color=self.purple_bg, hover_color="#5B2C6F", text_color="#FFFFFF", command=popup.destroy,
                      height=max(56, int(56 * FONT_SCALE)), width=240).pack(side="bottom", pady=(6, 14))
        ctk.CTkLabel(popup, text=ui("คำแนะนำทั่วไป ไม่ใช่การวินิจฉัย ทำตามแผนของแพทย์หรือนักกายภาพบำบัดของคุณเป็นหลัก",
                                    "General guidance, not a diagnosis. Follow your own doctor's or physiotherapist's plan first."),
                     font=ui_font(15, "regular", max_scale=1.2), text_color="#7A8A99",
                     wraplength=width - 60).pack(side="bottom", padx=24)
        # One section at a time, chosen with three large tabs: nothing to scroll,
        # and "when to get help" is always one tap away.
        tab_names = [title if i == 0 else name for i, ((title, _, _, _), name) in enumerate(
            zip(sections, (None, ui("หลังฝึก", "After practice"), ui("ควรพบแพทย์เมื่อไหร่", "When to get help"))))]
        tab_names[0] = ui("ตอนนี้", "Now")
        holder = ctk.CTkFrame(popup, fg_color="#FFFFFF")
        text_wrap = width - 120
        cards = []
        for title, color, background, tips in sections:
            card = ctk.CTkFrame(holder, fg_color=background, corner_radius=14)
            ctk.CTkLabel(card, text=title, font=ui_font(22, "semibold", max_scale=1.3), text_color=color, anchor="w",
                         justify="left", wraplength=text_wrap + 30).pack(fill="x", padx=18, pady=(12, 4))
            rows = ctk.CTkFrame(card, fg_color="transparent")
            rows.pack(fill="x", padx=(18, 14), pady=(0, 12))
            rows.grid_columnconfigure(1, weight=1)
            for row, tip in enumerate(tips):
                ctk.CTkLabel(rows, text="•", width=18, font=ui_font(20, "bold"), text_color=color).grid(
                    row=row, column=0, sticky="n", padx=(0, 8), pady=5)
                ctk.CTkLabel(rows, text=tip, font=ui_font(20, "regular", max_scale=1.25), text_color=self.black_fg,
                             wraplength=text_wrap, justify="left", anchor="w").grid(row=row, column=1, sticky="w", pady=4)
            cards.append(card)

        def show(name):
            for card in cards:
                card.pack_forget()
            cards[tab_names.index(name)].pack(fill="x")

        tabs = ctk.CTkSegmentedButton(popup, values=tab_names, command=show, font=ui_font(19, "semibold"),
                                      height=max(48, int(40 * FONT_SCALE)), selected_color=self.purple_bg,
                                      selected_hover_color="#3B1B48", unselected_color="#8E6BA3",
                                      unselected_hover_color="#7A5690", text_color="#FFFFFF",
                                      text_color_disabled=self.black_fg)
        tabs.pack(fill="x", padx=24, pady=(2, 8))
        holder.pack(fill="both", expand=True, padx=24, pady=(0, 4))
        tabs.set(tab_names[0])
        show(tab_names[0])
        popup.lift()
        if UI_LANGUAGE == "en":
            self._queue_voice("013.mp3")

    def record_completed_set(self):
        record = {
            "set_number": self.set,
            "completed_at": datetime.now().astimezone().isoformat(timespec="seconds"),
            "hand": self.target_hand_var.get(),
            "hold_seconds": self.time_max,
            "target_sets": self.target_sets_var.get(),
            "stable_poses": self._set_stable_poses,
            "total_poses": 15,
            "pain": self._last_pain,
        }
        self.completed_sets.append(record)
        self._save_report_state()
        self.write_log(f"SET_COMPLETE: {json.dumps(record, ensure_ascii=False)}")
        self._set_stable_poses = 0
        self.update_set_analysis()
        if self.history_page.winfo_ismapped():
            self.update_set_analysis()

    def _web_report_data(self):
        """Collect the report on the Tk thread as already-localised strings."""
        self.draw_five_day_trend()  # refreshes self._daily_pose_counts
        now = datetime.now().astimezone()
        partial = self.round * 5 + self.current_pose - 1
        total_poses = sum(item["total_poses"] for item in self.completed_sets) + partial
        steady = sum(item["stable_poses"] for item in self.completed_sets) + min(self._set_stable_poses, partial)
        active_days = sum(count > 0 for _, count in self._daily_pose_counts)
        stats = [
            (ui("เซตที่ทำเสร็จ", "Completed sets"), len(self.completed_sets)),
            (ui("ท่าที่ทำได้ทั้งหมด", "Poses completed"), total_poses),
            (ui("ท่าที่กล้องจับต่อเนื่อง", "Steady poses"), f"{steady}/{total_poses}"),
            (ui("วันที่ฝึกใน 5 วัน", "Days practiced (5)"), f"{active_days}/5"),
        ]
        trend = [(day.strftime("%d/%m"), count) for day, count in self._daily_pose_counts]
        sets = []
        for item in self.completed_sets:
            result, color, advice = assess_completed_set(item["stable_poses"])
            done_at = datetime.fromisoformat(item["completed_at"])
            pain = item.get("pain")
            sets.append({
                "number": item["set_number"],
                "heading": ui(f"เซตที่ {item['set_number']}", f"Set {item['set_number']}"),
                "result": result, "color": color, "advice": advice,
                "tip": improvement_tip(item["stable_poses"]),
                "rows": [
                    (ui("เวลา", "Time"), thai_datetime(done_at)),
                    (ui("มือที่ฝึก", "Hand"), hand_label(item["hand"])),
                    (ui("ทำครบ", "Completed"), ui(f"{item['total_poses']} ท่า (3 รอบ)",
                                                  f"{item['total_poses']} poses (3 rounds)")),
                    (ui("ค้างท่า", "Hold time"), ui(f"{item['hold_seconds']} วินาทีต่อท่า",
                                                    f"{item['hold_seconds']} s per pose")),
                    (ui("กล้องจับต่อเนื่อง", "Steady tracking"), f"{item['stable_poses']}/15"),
                    (ui("ความปวดที่บันทึก", "Reported pain"),
                     f"{pain}/10 · {pain_description(pain)}" if pain is not None
                     else ui("ไม่ได้บันทึก", "Not recorded")),
                ],
            })
        if partial:
            sets.append({
                "number": self.set + 1,
                "heading": ui(f"เซตที่ {self.set + 1} (ยังไม่ครบ)", f"Set {self.set + 1} (in progress)"),
                "result": ui("ทำถึงตรงนี้", "Saved so far"), "color": "#8191A1",
                "advice": ui(f"ทำไปแล้ว {partial} จาก 15 ท่า กลับมาทำต่อจากท่าที่ {self.current_pose} รอบที่ {self.round + 1} ได้",
                             f"{partial} of 15 poses done. Continue from pose {self.current_pose}, round {self.round + 1}."),
                "tip": ui("ระบบบันทึกความคืบหน้าไว้แล้ว แม้ปิดโปรแกรมก็ทำต่อได้",
                          "Progress is saved, even if the program is closed."),
                "rows": [
                    (ui("มือที่ฝึก", "Hand"), hand_label(self.target_hand_var.get())),
                    (ui("ทำแล้ว", "Done"), ui(f"{partial}/15 ท่า · ครบ {self.round}/3 รอบ",
                                             f"{partial}/15 poses · {self.round}/3 rounds")),
                    (ui("ค้างท่า", "Hold time"), ui(f"{self.time_max} วินาทีต่อท่า", f"{self.time_max} s per pose")),
                    (ui("กล้องจับต่อเนื่อง", "Steady tracking"), f"{min(self._set_stable_poses, partial)}/{partial}"),
                ],
            })
        pain_text, pain_color, pain_tip = pain_advice(self._pain_before, self._pain_after)
        # Plain-language summary for older readers: one sentence, one colour.
        before, after = self._pain_before, self._pain_after
        latest = after if after is not None else before
        sets_done = len(self.completed_sets)
        if latest is not None and (latest >= 7 or (before is not None and after is not None and after - before >= 2)):
            summary = (ui("วันนี้ควรพักมือ", "Rest your hand today"), "#B83228",
                       ui("ปวดมากขึ้นหลังฝึก" if before is not None and after is not None and after > before else "ระดับปวดสูง",
                          "Pain went up after practice" if before is not None and after is not None and after > before else "Pain is high"))
        elif sets_done and total_poses and steady / total_poses >= .8:
            summary = (ui("ทำได้ดีมาก", "Great work"), "#137A4B",
                       ui(f"ฝึกครบ {sets_done} เซต", f"{sets_done} {'set' if sets_done == 1 else 'sets'} done"))
        elif sets_done:
            summary = (ui("ทำครบแล้ว", "Well done"), "#A56A00",
                       ui(f"ฝึกครบ {sets_done} เซต ยังมีช่วงหยุดบ้าง", f"{sets_done} {'set' if sets_done == 1 else 'sets'} done, a few pauses"))
        else:
            summary = (ui("เริ่มต้นได้ดี", "A good start"), "#244B72",
                       ui(f"ทำไปแล้ว {total_poses} จาก 15 ท่า", f"{total_poses} of 15 poses so far"))
        thai_days = ("จ.", "อ.", "พ.", "พฤ.", "ศ.", "ส.", "อา.")
        en_days = ("Mon", "Tue", "Wed", "Thu", "Fri", "Sat", "Sun")
        days = [(ui(thai_days[day.weekday()], en_days[day.weekday()]), day.strftime("%d/%m"), count)
                for day, count in self._daily_pose_counts]
        tab_titles = (None, ui("ดูแลมือหลังฝึก", "Care after practice"), ui("เมื่อไหร่ควรไปพบแพทย์", "When to get help"))
        advice = []
        for (title, color, background, tips), fixed in zip(self._practice_tips(), tab_titles):
            advice.append({"title": fixed or ui("ตอนนี้ควรทำอย่างไร", "What to do now"),
                           "sub": None if fixed else title, "color": color, "background": background, "tips": tips})
        todo, doctor = self.short_advice()

        def pain_box(value):
            if value is None:
                return {"value": None, "word": ui("ยังไม่ได้เลือก", "Not chosen"), "color": "#7A8A99", "bg": "#F1EFF4"}
            color, bg = (("#1E8E4F", "#E3F4EA") if value <= 3 else ("#A56A00", "#FFF4DD") if value <= 6
                         else ("#B83228", "#FDECEA"))
            return {"value": value, "word": pain_description(value), "color": color, "bg": bg}
        if after is None:
            pain_result = (ui("ยังไม่ได้ใส่ความปวดหลังฝึก ให้เลือกที่หน้า \"ผลการฝึกของฉัน\" ในโปรแกรม แล้วส่งออกใหม่",
                              "Choose your pain after practice in the program to see the change"), "#A56A00", "#FFF4DD")
        elif before is None:
            pain_result = (ui(f"หลังฝึกปวดระดับ {after}", f"Pain after practice: {after}"), pain_box(after)["color"],
                           pain_box(after)["bg"])
        elif after < before:
            pain_result = (ui("ปวดลดลง ดีขึ้น", "Less pain, better"), "#1E8E4F", "#E3F4EA")
        elif after > before:
            pain_result = (ui("ปวดมากขึ้น ควรพัก", "More pain, rest"), "#B83228", "#FDECEA")
        else:
            pain_result = (ui("ปวดเท่าเดิม", "No change"), "#52667A", "#F1EFF4")
        simple = {
            "date": ui(f"{now.day} {('ม.ค.','ก.พ.','มี.ค.','เม.ย.','พ.ค.','มิ.ย.','ก.ค.','ส.ค.','ก.ย.','ต.ค.','พ.ย.','ธ.ค.')[now.month - 1]} "
                       f"{now.year + 543} · {now:%H:%M} น.", f"{now:%d %b %Y · %H:%M}"),
            "pain_boxes": [dict(pain_box(before), label=ui("ก่อนฝึก", "Before")),
                           dict(pain_box(after), label=ui("หลังฝึก", "After"))],
            "pain_result": {"text": pain_result[0], "color": pain_result[1], "bg": pain_result[2]},
            "todo": todo, "doctor": doctor,
            "day_dots": [(name, count > 0) for name, _, count in days],
            "poses": total_poses, "sets": sets_done,
        }
        return {
            "simple": simple,
            "summary": {"headline": summary[0], "color": summary[1], "detail": summary[2],
                        "icon": {"#137A4B": "ok", "#A56A00": "ok", "#B83228": "warn"}.get(summary[1], "info")},
            "hand": ui(f"มือ{self.target_hand_var.get()}", f"{hand_label(self.target_hand_var.get())} hand"),
            "tiles": [(str(total_poses), ui("ท่า", "poses"), ui("ทำได้ทั้งหมด", "Done in total")),
                      (str(sets_done), ui("เซต", "sets"), ui("ทำครบเซต", "Full sets")),
                      (f"{active_days}/5", ui("วัน", "days"), ui("วันที่ฝึก (5 วันล่าสุด)", "Days practised (last 5)"))],
            "pain_scale": {"before": before, "after": after,
                           "before_label": ui("ก่อนฝึก", "Before"), "after_label": ui("หลังฝึก", "After"),
                           "none": ui("ยังไม่ได้บันทึก", "Not recorded"),
                           "words": [pain_description(v) if v is not None else ui("ยังไม่ได้บันทึก", "Not recorded")
                                     for v in (before, after)],
                           "ends": (ui("ไม่ปวด", "No pain"), ui("ปวดมาก", "Severe"))},
            "advice": advice,
            "days": days,
            "lang": UI_LANGUAGE,
            "stats": stats, "trend": trend, "sets": sets,
            "pain": {"title": ui("ความปวดของมือ (0-10)", "Hand pain (0-10)"),
                     "headline": pain_text, "color": pain_color, "advice": pain_tip},
            "text": {
                "title": ui("ผลการฝึกบริหารนิ้ว", "Finger exercise results"),
                "generated": ui(f"ส่งออกเมื่อ{thai_datetime(now)}", f"Exported {thai_datetime(now)}"),
                "trend": ui("จำนวนท่าที่ทำสำเร็จ 5 วันล่าสุด", "Poses completed, last 5 days"),
                "sets": ui("รายละเอียดแต่ละเซต", "Each set"),
                "summary": ui("สรุปผลการฝึก", "Summary"),
                "hand": ui("มือที่ฝึก", "Hand"),
                "pain": ui("ความปวดของมือ", "Hand pain"),
                "advice": ui("คำแนะนำ", "Advice"),
                "days": ui("ฝึกครบกี่วัน (5 วันล่าสุด)", "Days practised (last 5)"),
                "poses": ui("ท่า", "poses"),
                "details": ui("ดูรายละเอียดแต่ละเซต", "Details of each set"),
                "n_poses": ui("ท่าที่ทำได้", "poses done"),
                "n_sets": ui("เซตที่ครบ", "full sets"),
                "todo": ui("ทำต่ออย่างไร", "What to do next"),
                "doctor": ui("ต้องไปหาหมอเมื่อ", "See a doctor if"),
                "all": ui("ดูรายงานทั้งหมด", "All reports"),
                "disclaimer": ui("คำแนะนำในหน้านี้เป็นคำแนะนำทั่วไป ไม่ใช่การวินิจฉัย ให้ทำตามแผนของแพทย์หรือนักกายภาพบำบัดเป็นหลัก",
                                 "This page gives general guidance, not a diagnosis. Follow your doctor's or physiotherapist's plan first."),
            },
        }

    def export_completed_sets(self):
        if not self.completed_sets and self.round == 0 and self.current_pose == 1:
            self.show_dialog(ui("ยังส่งออกไม่ได้", "Nothing to export yet"),
                             ui("ต้องทำท่าบริหารให้สำเร็จอย่างน้อย 1 ท่าก่อน\nจึงจะส่งออกผลเป็นเว็บได้",
                                "Finish at least one pose first, then you can share the results."), "warning")
            return
        stamp = datetime.now().strftime("%Y-%m-%d_%H-%M-%S")
        try:
            name = web_report.save_report(self._web_server.directory, self._web_report_data(), stamp)
            self._web_server.start(UI_LANGUAGE)
        except OSError as exc:
            logging.exception("Web export failed: %s", exc)
            self.show_dialog(ui("ส่งออกไม่สำเร็จ", "Export failed"),
                             ui("บันทึกหน้ารายงานหรือเปิดเว็บไม่ได้\nลองกดส่งออกใหม่อีกครั้ง",
                                "Could not save or share the report.\nPlease try again."), "error")
            return
        self.write_log(f"WEB_EXPORT: {name}")
        if UI_LANGUAGE == "en":
            self._queue_voice("014.mp3")
        self.show_report_qr(self._web_server.url(name))

    def show_report_qr(self, url):
        if self._qr_popup is not None and self._qr_popup.winfo_exists():
            self._qr_popup.destroy()
        popup = ctk.CTkToplevel(self)
        self._qr_popup = popup
        popup.title(ui("สแกนดูผลการฝึก", "Scan to view results"))
        popup.configure(fg_color="#FFFFFF")
        width, height = self.screen_width, self.screen_height
        popup.geometry(f"{width}x{height}+0+0")
        popup.transient(self)
        popup.bind("<Escape>", lambda e: popup.destroy())
        try:
            popup.attributes("-fullscreen", True)
        except tk.TclError:
            pass
        popup.lift()
        popup.after(100, popup.focus_force)
        title_font = ui_font(max(30, int(44 * self.u_scale)), "bold")
        note_font = ui_font(max(20, int(28 * self.u_scale)), "regular")
        button_h = max(60, int(90 * self.scale_h))
        ctk.CTkLabel(popup, text=ui("สแกนเพื่อดูผลการฝึก", "Scan to view results"),
                     font=title_font, text_color=self.purple_bg).pack(pady=(int(height * .04), 8))
        # Leave room for the title, the Wi-Fi note and the close button.
        qr_side = max(200, min(int(width * .8), height - int(height * .04) - button_h - 230))
        image = web_report.qr_image(url)
        if image is not None:
            self._qr_photo = ctk.CTkImage(light_image=image, size=(qr_side, qr_side))
            ctk.CTkLabel(popup, image=self._qr_photo, text="").pack(pady=4)
        else:
            ctk.CTkLabel(popup, text=ui("ไม่มีแพ็กเกจ qrcode จึงแสดง QR ไม่ได้",
                                        "qrcode package missing; cannot show the QR code"),
                         font=note_font, text_color="#B83228").pack(expand=True)
        offline = url.startswith("http://127.")
        ctk.CTkLabel(popup, text=(ui("เครื่องยังไม่ได้ต่อเครือข่าย มือถือจะเปิดลิงก์นี้ไม่ได้",
                                     "This device is not on a network; phones cannot open this link.")
                                  if offline else
                                  ui("มือถือต้องต่อ Wi-Fi เดียวกับเครื่องนี้",
                                     "The phone must be on the same Wi-Fi as this device.")),
                     font=note_font, text_color="#B83228" if offline else "#43566A",
                     wraplength=width - 80).pack(padx=40, pady=(8, 10))
        ctk.CTkButton(popup, text=ui("ปิด", "Close"), font=ui_font(max(26, int(34 * self.u_scale)), "semibold"),
                      fg_color=self.purple_bg, hover_color="#5B2C6F", text_color="#FFFFFF",
                      command=popup.destroy, height=button_h,
                      width=max(240, int(width * .22)), corner_radius=14).pack(pady=(4, 16))

    def _queue_voice(self, filename, wait=False):
        """Play a clip. wait=True lets the clip that is playing finish first
        (used after "start" so the start announcement is never cut off)."""
        with self._voice_condition:
            if self._voice_stopping:
                return
            self._voice_revision += 1
            self._voice_pending = (filename, UI_LANGUAGE, self._voice_revision, wait)
            self._voice_condition.notify_all()

    def _voice_path(self, filename, language):
        if language != "en":
            return os.path.join(os.path.dirname(os.path.abspath(__file__)), "Voices", filename)
        if getattr(self, "_voice_cache_dir", None) is None:
            self._voice_cache_dir = tempfile.mkdtemp(prefix="anti-finger-voice-")
        path = os.path.join(self._voice_cache_dir, filename)
        if not os.path.exists(path):
            with open(path, "wb") as output:
                output.write(base64.b64decode(ENGLISH_VOICE_CLIPS[filename]))
        return path

    def _voice_loop(self):
        """One long-running `mpg123 -R` plays every clip.

        Starting a new mpg123 for each clip (and killing the old one) made the
        sound card reopen every time, which on the Pi can swallow the start of
        a clip; that is why "เริ่มต้นใช้งาน" was cut short from the second press
        on. A single player keeps the audio device open and switches clips
        instantly; it reports "@P 0" when a clip has finished.
        """
        player = shutil.which("mpg123")
        if not player:
            logging.warning("Voice playback requires mpg123")
        process = None
        idle = threading.Event()
        idle.set()

        def reader(proc):
            for line in proc.stdout:
                if line.startswith(("@I", "@P")):
                    logging.debug("mpg123 %s", line.strip())
                if line.startswith("@P 2"):
                    idle.clear()
                elif line.startswith("@P 0") or line.startswith("@E"):
                    idle.set()
            idle.set()

        def send(command):
            nonlocal process
            if process is None or process.poll() is not None:
                extra = os.environ.get("MPG123_OPTIONS", "").split()
                process = subprocess.Popen([player, "-R", *extra], stdin=subprocess.PIPE,
                                           stdout=subprocess.PIPE, stderr=subprocess.DEVNULL,
                                           text=True, bufsize=1)
                threading.Thread(target=reader, args=(process,), name="voice-reader", daemon=True).start()
                process.stdin.write("SILENCE\n")
            process.stdin.write(command + "\n")
            process.stdin.flush()

        try:
            while True:
                with self._voice_condition:
                    self._voice_condition.wait_for(lambda: self._voice_pending or self._voice_stopping)
                    if self._voice_stopping:
                        return
                    filename, language, revision, wait = self._voice_pending
                    self._voice_pending = None
                if not player:
                    continue
                if wait:
                    # Let the current clip end; give up waiting if a newer request arrives.
                    deadline = time.monotonic() + 15
                    while not idle.wait(.05) and time.monotonic() < deadline:
                        with self._voice_condition:
                            if self._voice_revision != revision or self._voice_stopping:
                                break
                    with self._voice_condition:
                        if self._voice_revision != revision:
                            continue
                try:
                    if filename is None:
                        if process is not None and process.poll() is None:
                            send("STOP")
                        continue
                    path = self._voice_path(filename, language)
                    if not os.path.isfile(path):
                        logging.warning("Audio file missing: %s", path)
                        continue
                    idle.clear()
                    send("LOAD " + path)
                except (OSError, KeyError, ValueError):
                    logging.exception("Voice playback failed for %s", filename)
                    process = None
                    idle.set()
        finally:
            if process is not None and process.poll() is None:
                try:
                    process.stdin.write("QUIT\n")
                    process.stdin.flush()
                    process.wait(timeout=1)
                except (OSError, ValueError, subprocess.TimeoutExpired):
                    process.kill()

    def show_main_page(self):
        self.history_page.pack_forget()
        self.main_content_frame.pack(side="top", fill="both", expand=True, padx=8, pady=4)
        self._queue_voice(self.pose_sounds[self.current_pose][0] if self.running else "010.mp3")

    def show_history_page(self):
        self.goal_popup.place_forget()
        self.main_content_frame.pack_forget()
        self._queue_voice("009.mp3")
        self.history_page.pack(side="top", fill="both", expand=True)
        self.update_set_analysis()

    def write_log(self, message):
        now = datetime.now().strftime("[%Y-%m-%d %H:%M:%S]")
        log_message = f"{now} เซตที่ {self.set} รอบที่ {self.round} : {message}"
        try:
            BASE_DIR = os.path.dirname(os.path.abspath(__file__))
            FILE_PATH = os.path.join(BASE_DIR, "Anti-Finger.txt")
            with open(FILE_PATH, "a", encoding="utf-8") as f:
                f.write(log_message + "\n")
            self._daily_pose_cache_time = 0.0
        except Exception:
            pass

    def _start_video(self):
        if self._closing:
            return
        cv2.setNumThreads(1)
        self.cam_thread = threading.Thread(
            target=self._camera_feed_loop, name="camera", daemon=True)
        self._workers.append(self.cam_thread)
        self.cam_thread.start()
        if not self._preview_only:
            self.ai_thread = threading.Thread(
                target=self._ai_processing_loop, name="inference", daemon=True)
            self._workers.append(self.ai_thread)
            self.ai_thread.start()
        self._poll_camera()

    def _update_camera_label(self, pil_image, match, env_txt, env_col):
        # All calls to Tk/CustomTkinter stay on the main thread.
        if pil_image is not None:
            self.camera_photo.configure(light_image=pil_image)
        self.match_badge.configure(
            text=ui("พบมือแล้ว", "Hand found") if match else ui("กำลังหามือ", "Looking for hand"),
            text_color="#2ECC71" if match else "#E74C3C")
        self.env_badge.configure(text=env_txt, text_color=env_col)

    def _camera_feed_loop(self):
        cap = None
        try:
            cap = cv2.VideoCapture(self.camera_path, cv2.CAP_V4L2)
            if not cap.isOpened():
                raise RuntimeError(f"Cannot open {self.camera_path}")
            cap.set(cv2.CAP_PROP_FRAME_WIDTH, 320)
            cap.set(cv2.CAP_PROP_FRAME_HEIGHT, 240)
            cap.set(cv2.CAP_PROP_BUFFERSIZE, 1)  # Backend may ignore this.
            logging.info("Camera %s: backend=%s, negotiated=%sx%s",
                         self.camera_path, cap.getBackendName(),
                         cap.get(cv2.CAP_PROP_FRAME_WIDTH),
                         cap.get(cv2.CAP_PROP_FRAME_HEIGHT))
            failures = 0
            while not self._stop_video.is_set():
                ok, frame = cap.read()
                if not ok or frame is None or frame.size == 0:
                    failures += 1
                    with self.frame_lock:
                        self.latest_frame = None
                        self.camera_error = ui(f"อ่านกล้องไม่ได้ ({failures}/10)",
                                               f"Camera read failed ({failures}/10)")
                    if failures >= 10:
                        raise RuntimeError("Camera read failed 10 times; check device/USB")
                    self._stop_video.wait(0.1)
                    continue
                failures = 0
                frame = cv2.flip(frame, 1)
                with self.frame_lock:
                    self.latest_frame = frame
                    self.frame_seq += 1
                    self.frame_time = time.monotonic()
                    self.camera_error = None
        except Exception as exc:
            logging.exception("Camera worker failed")
            with self.frame_lock:
                self.latest_frame = None
                self.camera_error = str(exc)
        finally:
            if cap is not None:
                cap.release()
            logging.info("Camera worker stopped; capture released")

    def _poll_camera(self):
        if self._closing:
            return
        try:
            now = time.monotonic()
            with self.frame_lock:
                self.ai_pose = self.current_pose
                self.ai_target_hand = self.target_hand_var.get()
                frame = self.latest_frame
                seq, captured = self.frame_seq, self.frame_time
                camera_error, ai_error = self.camera_error, self.ai_error
                timely = result_is_timely(now,self.result_time,self.result_completed)
                fresh_result = self.result_pose == self.current_pose and timely
                wrong_or_unknown_side = (self.latest_observed_present and fresh_result
                                         and self.latest_hand != self.ai_target_hand)
                healthy = (fresh_result and not ai_error and not camera_error and not self._preview_only
                           and frame is not None and 0 <= now-captured < .8
                           and self.result_target_hand == self.ai_target_hand
                           and not wrong_or_unknown_side)
                context = (self.current_pose,self.ai_target_hand,self.running,self.countdown_active,self.result_track_id)
                match,self._match_state,self._match_confirmed = self._match_gate.update(
                    now,self.result_seq,self.result_completed,self.latest_match,self.latest_present,healthy,context)
                self._match_updated = now
                overlay_fresh = (not ai_error and not camera_error and not self._preview_only
                                 and result_is_timely(now,self.overlay_time,self.overlay_completed)
                                 and now-self.overlay_completed <= 1.0 and now-captured < .8)
                points = self.latest_overlay_points if overlay_fresh else None
                presence_healthy = (not ai_error and not camera_error and not self._preview_only
                                    and frame is not None and 0 <= now-captured < .8 and timely
                                    and self.result_target_hand == self.ai_target_hand
                                    and not wrong_or_unknown_side)
                hand_detected = self._presence_latch.update(
                    now,self.result_seq,self.result_completed,self.latest_present,presence_healthy)
                currently_seen = self.latest_present and timely and 0 <= now-self.result_completed <= 1.0
                overlay_key = (seq, self.overlay_time if points is not None else None)
                env_txt, env_col = self.latest_env_text, self.latest_env_color
            pil_image = None
            if frame is None or now - captured > 1.0 or camera_error:
                match = False
                if frame is not None and self._displayed_seq != (seq, None):
                    pil_image = ImageOps.fit(
                        Image.fromarray(cv2.cvtColor(frame, cv2.COLOR_BGR2RGB)),
                        (self.camera_width, self.camera_height),
                        method=Image.Resampling.BILINEAR)
                    self._displayed_seq = (seq, None)
                elif frame is None and self._displayed_seq is not None:
                    pil_image = Image.new("RGB", (self.camera_width, self.camera_height), (220,220,220))
                    self._displayed_seq = None
                env_txt = (ui("กล้องไม่พร้อม · ตรวจสายและอุปกรณ์", "Check the camera cable")
                           if camera_error else ui("กล้อง: ยังไม่มีเฟรมใหม่", "Camera: no new frame"))
                env_col = "#E74C3C"
            else:
                if overlay_key != self._displayed_seq:
                    pil_image = ImageOps.fit(
                        Image.fromarray(cv2.cvtColor(draw_hand_overlay(frame, points), cv2.COLOR_BGR2RGB)),
                        (self.camera_width, self.camera_height),
                        method=Image.Resampling.BILINEAR)
                    self._displayed_seq = overlay_key
                if self._preview_only:
                    match, env_txt, env_col = False, ui("ทดสอบกล้อง: ปิด AI", "Camera test: AI off"), "#F39C12"
                elif ai_error:
                    match, env_txt, env_col = False, ui("AI: ยังไม่พร้อม ตรวจบันทึกข้อผิดพลาด", "AI unavailable. Check the error log."), "#E74C3C"
                elif not fresh_result:
                    match, env_txt, env_col = False, ui("AI: รอผลใหม่", "Checking your pose"), "#F39C12"
            if match and self._match_state == "grace":
                env_txt,env_col = ui("กำลังติดตามต่อ...", "Tracking hand..."), "#F39C12"
            self.set_hand_posit_state(match)
            if hand_detected and not currently_seen:
                env_txt,env_col = ui("ติดตามมือขาดช่วง · กำลังตรวจซ้ำ", "Hold still · checking again"), "#F39C12"
            elif hand_detected:
                env_txt = ui("พบมือ · ", "Hand found · ") + (
                    ui("ยืนยันท่าแล้ว", "Pose confirmed") if self._match_confirmed else
                    ui("กำลังติดตามต่อ", "Tracking") if match else
                    ui("ยังยืนยันท่าไม่ได้", "Adjust your pose"))
            self._update_camera_label(pil_image, hand_detected, env_txt, env_col)
        except Exception:
            self.set_hand_posit_state(False)
            logging.exception("Camera GUI update failed")
        finally:
            if not self._closing:
                self._video_job = self.after(50, self._poll_camera)

    def _ai_processing_loop(self):
        try:
            self._run_ai_inference()
        except Exception as exc:
            logging.exception("AI worker failed; camera preview remains independent")
            with self.frame_lock:
                self.latest_match = False
                self.result_time = 0.0
                self.ai_error = str(exc)

    def _run_ai_inference(self):
        try:
            from tflite_runtime.interpreter import Interpreter
        except ImportError:
            import tensorflow as tf
            Interpreter = tf.lite.Interpreter
        model_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "hand_landmark.tflite")
        ai_threads=max(1,min(2,int(os.environ.get("AI_THREADS","2"))))
        logging.info("TFLite CPU threads=%s",ai_threads)
        interpreter = Interpreter(model_path=model_path,num_threads=ai_threads)
        interpreter.allocate_tensors()
        import hashlib
        with open(model_path,'rb') as model_file:
            logging.info("Configured landmark model: %s sha256=%s",model_path,
                         hashlib.sha256(model_file.read()).hexdigest())
        interpreter = ensure_handedness_model(
            Interpreter,interpreter,os.path.dirname(model_path),ai_threads)
        detector = load_palm_detector(Interpreter,os.path.dirname(model_path),ai_threads)
        tracker = StableLocalTracker(interpreter,detector)
        logging.info("Hand tracker mode=%s", "palm_roi" if detector is not None else "legacy")
        last_seq = -1
        log_started = time.monotonic()
        inference_times = []
        found_samples = matched_samples = max_misses = 0
        reasons,stages = defaultdict(int),defaultdict(int)
        previous_palm_calls = previous_hand_calls = 0
        # One landmark call; palm detection only for acquisition/recovery.
        while not self._stop_video.wait(.06):
            with self.frame_lock:
                if self.latest_frame is None or self.frame_seq == last_seq:
                    continue
                frame = self.latest_frame.copy()
                last_seq,captured = self.frame_seq,self.frame_time
                pose,target = self.ai_pose,self.ai_target_hand
            if time.monotonic()-captured > .8:
                continue
            started = time.monotonic()
            points,matched,track_id = tracker.process(frame,captured,pose,target)
            completed = time.monotonic()
            observed = tracker.last_hand if points is not None else None
            inference_times.append((completed-started)*1000)
            if completed-captured > 1.2:
                # A newly completed, excessively old result is not fresh evidence.
                points,matched = None,False
                observed = None
                tracker.last_reason = "result_too_old"
            selected_present = points is not None and observed == target
            matched = bool(matched and selected_present)
            found_samples += points is not None
            matched_samples += bool(matched)
            max_misses = max(max_misses,tracker.misses)
            reasons[tracker.last_reason] += 1
            stages[tracker.stage] += 1
            if time.monotonic()-log_started >= 3:
                logging.info(
                    "Tracking found=%s/%s matched=%s mean=%.0fms max=%.0fms age=%.0fms "
                    "score=%.3f palm_score=%.3f left_score=%.3f hand=%s target=%s reason=%s miss=%s maxmiss=%s "
                    "stage=%s roi=%s calls=palm:%s,hand:%s reasons=%s stages=%s",
                    found_samples,len(inference_times),matched_samples,
                    sum(inference_times)/len(inference_times),max(inference_times),
                    (time.monotonic()-captured)*1000,tracker.last_score,
                    tracker.last_palm_score,tracker.last_handedness_score,
                    tracker.last_hand or 'unknown',target,tracker.last_reason,tracker.misses,max_misses,
                    tracker.stage,tracker.roi_description(),
                    tracker.palm_calls-previous_palm_calls,tracker.hand_calls-previous_hand_calls,
                    dict(reasons),dict(stages))
                previous_palm_calls,previous_hand_calls = tracker.palm_calls,tracker.hand_calls
                inference_times.clear()
                reasons.clear()
                stages.clear()
                found_samples = matched_samples = max_misses = 0
                log_started=time.monotonic()
            with self.frame_lock:
                self.latest_match = matched
                self.latest_present = selected_present
                self.latest_observed_present = points is not None
                self.latest_hand = observed
                if points is not None:
                    self.latest_overlay_points = points[:,:2].copy()
                    self.overlay_time = captured
                    self.overlay_completed = completed
                if selected_present:
                    self.latest_env_text,self.latest_env_color = ui("พบมือ" + target,
                                                                      hand_label(target) + " hand found"),"#2ECC71"
                elif points is None:
                    self.latest_env_text,self.latest_env_color = ui("กำลังค้นหามือ...", "Looking for your hand"),"#F39C12"
                elif tracker.handedness is None:
                    self.latest_env_text,self.latest_env_color = ui("โมเดลไม่มีข้อมูลแยกมือซ้าย/ขวา",
                                                                      "Cannot tell left from right"),"#E74C3C"
                elif observed is None:
                    self.latest_env_text,self.latest_env_color = ui("พบมือ แต่ยังแยกข้างไม่ชัด",
                                                                      "Hand found, side unclear"),"#F39C12"
                else:
                    self.latest_env_text,self.latest_env_color = (
                        ui("พบมือ" + observed + " · โปรดใช้มือ" + target,
                           hand_label(observed) + " hand found · use " + hand_label(target)),"#F39C12")
                self.result_time,self.result_pose = captured,pose
                self.result_completed = completed
                self.result_seq,self.result_track_id = last_seq,track_id
                self.result_target_hand = target

    def set_hand_posit_state(self, match):
        self.is_pose_currently_matched = match

    def timer_reset(self):
        self.time_current = self.time_max
        self.update_timer_display()
        self.reset_pic()
        self.set_breathing("เตรียมพร้อม...", "Get ready", "#52667A")
        try:
            self.update_EX_pose()
        except Exception:
            pass

    def reset_pic(self):
        self.timer_canvas.delete("progress")
        l = self.timer_pad
        r = self.timer_canvas_size - self.timer_pad
        self.timer_canvas.create_oval(l, l, r, r, outline=self.green_btn, width=10, tags="progress")

    def update_timer_display(self):
        try:
            progress = max(0.0, min(1.0, (self.time_max - self.time_current) / float(self.time_max)))
            extent = 360 * progress
            self.timer_canvas.delete("progress")
            l = self.timer_pad
            r = self.timer_canvas_size - self.timer_pad
            self.timer_canvas.create_arc(l, l, r, r, start=-90, extent=-extent, style="arc", width=10, outline=self.green_btn, tags="progress")
            
            display_time = int(math.ceil(self.time_current))
            self.timer_canvas.itemconfig(self.timer_text, text=str(display_time))
        except Exception:
            pass

    def reset_feedback(self):
        self.set_feedback("ลุยท่าต่อไปได้เลย!", "Ready for the next pose", "#F39C12")

    def update_text(self):
        self.Label_pose_action_text.configure(text=self.pose_name_en[self.current_pose]
                                              if UI_LANGUAGE == "en" else self.pose_labels_th[self.current_pose])
        self.Label_pose_thai_text.configure(text=ui(f"ท่าที่ {self.current_pose}", f"Pose {self.current_pose}"))

    def update_round(self):
        self.Label_set_times_number.configure(text=f"{self.round}")
        self.Label_set_number.configure(text=f"{self.set}")
        self.round_progress.set(self.round / 3.0)

        target = self.target_sets_var.get()
        if self.set == 0 and self.round == 0:
            reward_msg = ui("พร้อมแล้ว เริ่มลุยเลย!", "Ready to start")
            color = "#F39C12"
        elif self.round == 0 and self.set > 0:
            reward_msg = ui(f"สุดยอด! จบเซตที่ {self.set} แล้ว!",
                            f"Set {self.set} complete")
            color = "#27AE60"
        else:
            reward_msg = ui(f"ลุยต่อ! เซตที่ {self.set + 1} · รอบที่ {self.round}/3",
                            f"Set {self.set + 1} · rounds {self.round}/3")
            color = "#D35400"
        self.reward_label.configure(text=reward_msg, text_color=color)

    def update_EX_pose(self):
        BASE_DIR = os.path.dirname(os.path.abspath(__file__))
        try:
            img_size = self.reference_image_size
            pose_path = os.path.join(BASE_DIR, "pictures", "EX_POSE", f"pose{self.current_pose}.png")
            small_hand_image_pil = Image.open(pose_path)
            self.small_hand_photo = ctk.CTkImage(light_image=small_hand_image_pil, size=(img_size, img_size))
            self.small_hand_label.configure(image=self.small_hand_photo)
        except:
            pass

    def _start_label(self):
        if self.current_pose > 1 or self.round > 0:
            return ui("▶ ทำต่อ", "▶ Continue")
        if self.set > 0:
            return ui("▶ เริ่มเซตถัดไป", "▶ Next set")
        return ui("▶ เริ่มต้น", "▶ Start")

    def toggle_start_pause(self):
        if not self.running and not self.countdown_active:
            self.start_stop_button.configure(text=ui("หยุด", "Pause"), fg_color=self.yellow_btn, hover_color=self.hover_yellow_bt)
            self._queue_voice("006.mp3")
            self.start_pose_countdown(3)
        else:
            self.start_stop_button.configure(text=self._start_label(), fg_color=self.green_btn, hover_color=self.hover_green_bt)
            self.running = False
            self._cancel_countdown()
            self._queue_voice("007.mp3")

    def start_pose_countdown(self, seconds: int):
        self._cancel_countdown()
        self.countdown_active = True
        self.countdown_total = max(1, seconds)
        self.countdown_end_time = time.time() + self.countdown_total
        self.countdown_job = self.after(0, self._animate_countdown)

    def _animate_countdown(self):
        if not self.countdown_active:
            return
        now = time.time()
        remaining = self.countdown_end_time - now
        if remaining <= 0:
            self.countdown_active = False
            self.countdown_job = None
            self.running = True
            self.is_pose_currently_matched = False
            try:
                display_time = int(math.ceil(self.time_current))
                self.timer_canvas.itemconfig(self.timer_text, text=str(display_time))
                self.timer_canvas.delete("progress")
                l = self.timer_pad
                r = self.timer_canvas_size - self.timer_pad
                self.timer_canvas.create_oval(l, l, r, r, outline=self.green_btn, width=10, tags="progress")
            except Exception:
                pass
            if self.main_content_frame.winfo_ismapped():
                self._queue_voice(self.pose_sounds[self.current_pose][0], wait=True)
            return

        frac = max(0.0, min(1.0, remaining / float(self.countdown_total)))
        extent = 360 * frac
        try:
            self.timer_canvas.delete("progress")
            l = self.timer_pad
            r = self.timer_canvas_size - self.timer_pad
            self.timer_canvas.create_arc(l, l, r, r, start=-90, extent=-extent, style="arc", width=10, outline="#FFA500", tags="progress")
            secs = int(math.ceil(remaining))
            self.timer_canvas.itemconfig(self.timer_text, text=str(secs))
        except Exception:
            pass

        try:
            self.countdown_job = self.after(50, self._animate_countdown)
        except Exception:
            self.countdown_active = False
            self.countdown_job = None

    def _cancel_countdown(self):
        if self.countdown_active:
            self.countdown_active = False
            if self.countdown_job:
                try:
                    self.after_cancel(self.countdown_job)
                except Exception:
                    pass
                self.countdown_job = None
            try:
                display_time = int(math.ceil(self.time_current))
                self.timer_canvas.itemconfig(self.timer_text, text=str(display_time))
                self.timer_canvas.delete("progress")
                l = self.timer_pad
                r = self.timer_canvas_size - self.timer_pad
                self.timer_canvas.create_oval(l, l, r, r, outline=self.green_btn, width=10, tags="progress")
            except Exception:
                pass

    def reset_action(self, confirm=True):
        if confirm and (self.completed_sets or self.round or self.current_pose > 1) and not self.show_dialog(
                ui("ล้างผลการฝึกทั้งหมด?", "Clear all results?"),
                ui("ผลการฝึกและความปวดที่บันทึกไว้จะถูกลบ\nแล้วเริ่มนับใหม่ตั้งแต่ต้น",
                   "Saved practice and pain results will be deleted and counting starts again."),
                "question", yes=ui("ล้างและเริ่มใหม่", "Clear and restart"), no=ui("ยกเลิก", "Cancel")):
            return
        self.running = False
        try:
            self._cancel_countdown()
        except Exception:
            pass
        self.start_stop_button.configure(text=self._start_label(), fg_color=self.green_btn, hover_color=self.hover_green_bt)
        self.round = 0
        self.set = 0
        self.completed_sets.clear()
        self._set_stable_poses = 0
        self._pose_had_long_pause = False
        self._pose_pause_started = None
        self._last_pain = None
        self._pain_before = None
        self._pain_after = None
        self._editing_after_pain = False
        self._goal_reached = False
        self._report_started_at = datetime.now().astimezone()
        self._clear_report_storage()
        self._daily_pose_counts = []
        self._daily_pose_cache_time = 0.0
        self._save_report_state()
        self.current_pose = 1
        self._save_report_state()
        self.update_set_analysis()
        self.timer_reset()
        self.update_text()
        self.update_round()
        self.reset_feedback()
        self.update_live_report()
        self._queue_voice("008.mp3" if confirm else None)

    def on_close(self):
        if self._closing:
            return
        self._closing = True
        self.running = False
        try:
            self._web_server.stop()
        except Exception:
            logging.exception("Cannot stop web report server")
        self.set_hand_posit_state(False)
        self._stop_video.set()
        with self._voice_condition:
            self._voice_stopping = True
            self._voice_revision += 1
            self._voice_condition.notify_all()
        for attr in ("_video_job", "_sensor_job", "countdown_job"):
            job = getattr(self, attr, None)
            if job is not None:
                self.after_cancel(job)
                setattr(self, attr, None)
        self._close_started = time.monotonic()
        self._close_warned = False
        self._wait_for_video_stop()

    def _wait_for_video_stop(self):
        # Keep Tk alive while workers finish. Never release during cap.read().
        if any(worker.is_alive() for worker in self._workers):
            if not self._close_warned and time.monotonic() - self._close_started > 3:
                logging.error("Waiting for camera/AI native call to finish; "
                              "if stuck, identify and terminate this application's PID")
                self.env_badge.configure(text=ui("กำลังรอปิดกล้อง/AI...", "Closing camera and AI..."), text_color="#E74C3C")
                self._close_warned = True
            self.after(50, self._wait_for_video_stop)
            return
        for worker in self._workers:
            worker.join(timeout=0)
        self.destroy()

    def check_sensor_loop(self):
        if self._closing:
            return
        now = time.monotonic()
        if now - self._last_report_expiry_check >= 60:
            self._last_report_expiry_check = now
            self._expire_report_if_needed()
        if now - self._last_live_report_update >= 1:
            self._last_live_report_update = now
            if self.history_page.winfo_ismapped():
                self.update_live_report()
        dt = max(0.0,now-self._last_sensor_tick)
        self._last_sensor_tick = now
        if dt > .5:
            self._match_gate.reset()
            self.set_hand_posit_state(False)
            self._match_confirmed = False
        if self.running:
            with self.frame_lock:
                matched = (getattr(self, "is_pose_currently_matched", False)
                           and self.latest_frame is not None
                           and self.camera_error is None
                           and self.ai_error is None
                           and self.result_pose == self.current_pose
                           and self.result_target_hand == self.target_hand_var.get()
                           and not (self.latest_observed_present
                                    and self.latest_hand != self.target_hand_var.get())
                           and result_is_timely(now,self.result_time,self.result_completed)
                           and now-self.frame_time < .8
                           and now-self._match_updated < .25
                           and dt <= .5)
            if matched:
                self._pose_pause_started = None
                if self.time_current > 0:
                    self.time_current = max(0.0,self.time_current-min(dt,.25)) 
                    self.update_timer_display()
                    elapsed = self.time_max - self.time_current
                    if elapsed <= 2:
                        self.set_breathing("สูดหายใจเข้า...", "Breathe in", self.blue_btn)
                    else:
                        self.set_breathing("ผ่อนลมหายใจ...", "Breathe out", self.green_btn)

                if self.time_current <= 0 and self._match_confirmed and now-self.result_completed <= .35:
                    self._on_pose_success()
            else:
                if self.time_current < self.time_max and not self._pose_had_long_pause:
                    if self._pose_pause_started is None:
                        self._pose_pause_started = now
                    elif now - self._pose_pause_started >= 1.5:
                        self._pose_had_long_pause = True
                self.set_breathing("พักเวลาไว้ · จัดมือใหม่เมื่อพร้อม",
                                   "Paused · adjust your hand", "#E74C3C")

        try:
            self._sensor_job = self.after(100, self.check_sensor_loop)
        except Exception:
            pass

    def _on_pose_success(self):
        set_finished = False
        if not self._pose_had_long_pause:
            self._set_stable_poses += 1
        self._pose_had_long_pause = False
        self._pose_pause_started = None
        try:
            completed_pose_name = self.pose_name[self.current_pose]
            self.write_log(f"ท่า {completed_pose_name} สำเร็จ!")
            
            encouragements = [("เก่งมาก!", "Well done!"), ("ยอดเยี่ยม!", "Excellent!"),
                              ("เป๊ะมาก!", "Great work!"), ("สุดยอด!", "You did it!")]
            thai, english = random.choice(encouragements)
            self.set_feedback(thai, english, "#137A4B")
            self.set_breathing("ผ่อนคลาย...", "Relax...", "#BDC3C7")
        except Exception:
            pass

        self.current_pose += 1
        if self.current_pose > 5:
            self.current_pose = 1
            self.round += 1
            
            if self.round >= 3:
                self.round = 0
                self.set += 1
                self.record_completed_set()
                set_finished = True
                self.running = False
                self.start_stop_button.configure(text=self._start_label(), fg_color=self.green_btn,
                                                 hover_color=self.hover_green_bt)
                self.trigger_goal_popup(self.set)

        try:
            self.update_round()
            self.timer_reset()
            self.update_EX_pose()
            self.update_text()
            self.after(2500, self.reset_feedback)
            
            self._save_report_state()  # keep progress even if the set is not finished
            if set_finished:
                self._queue_voice("011.mp3" if UI_LANGUAGE == "en" else None)
            elif self.main_content_frame.winfo_ismapped():
                self._queue_voice(self.pose_sounds[self.current_pose][0])
        except Exception:
            pass

# English prompts rendered with Piper en_US-ljspeech-medium (public domain training audio).
# https://huggingface.co/rhasspy/piper-voices/blob/main/en/en_US/ljspeech/medium/MODEL_CARD
# Pre-rendered MP3s keep playback offline and avoid running speech synthesis on the Pi.
ENGLISH_VOICE_CLIPS = {
    '001.mp3': (  # Open your hand and straighten your fingers.
        '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'
        'qqqqqqqqqqqqqg=='
    ),
    '002.mp3': (  # Curl your fingers into a hook. Keep your knuckles straight.
        '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'
        'CtURK3X73YAlTZnmFAqVIFuYDROlBYQmksZJMU5LHhmpGHV4GXyoJQTyMTRZOlCYy4a8XExp/+Wf/3WMaCgoVRipy9za'
        'Q//zUMREGcH+ll4JhhRDHgqGj5EtCTA2GtvaLuOlix1ytLuIqIlO8rJZ76moI/VRFw04/L/v4DNv+zk1kNGAqQ/QWGo4'
        'U6AGznICVBHxH1iIIDbEJHI9pDGrKMlSfe57k31QZUlX/9Nei16MoVDocrowYMOz1f+ntttXv/37dVgy7Bz/81LEUhny'
        'xpJeMMTYXc15dQu69ktqQil25Si5ikol6iB4VTOTHLbiDJL/6cRGlMIVQIQChvpJJOio6W4gQseJIe8aDA7NMjw6ApTK'
        'ORyEikEpWBRDu7JXr////9n/sJYtemaDuk0Te4lkDGL+Ykd15lJWpx8W2SN+54couuckROqr7P/zUMRgGgoKgb9JGABh'
        'onnVlg3chSogQCsUCAUDAYCQQBgICI3g7J+A0HFMWhMNf1Go7+ccJm/xsLjxwv/5QSgiMJIb//6sg4GwDS39E/4QjQIg'
        'JgixURQIS//oKpDSgo////0VTEFNRTQuMFVVVUxBTUU0LjBVVVVVVVVVVVVVVVX/81LEbBOZ3oJfhzgAVVVVVVVVVVVV'
        'VVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVV'
        'VVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVf/zUsSJAAADSAHAAABVVVVVVVVVVVVVVVVVVVVV'
        'VVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVV'
        'VVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVV'
    ),
    '003.mp3': (  # Close your hand into a full fist.
        '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'
        'GoJqsZ9PKALPMuCjcMXx1l05oczQNFjVSogHREQm8tr0fW+Zp9wX0KkKyH7aUMqlDnczj//////9s4v/jWPn9gcEIb2d'
        'RyRGTN7/////////////////cd58ZvH3qemtSx///+OMKkRa07W3KOGEGxBtaFR65qAAyiR7Ai9T//NQxNIuixqKX5l4'
        'ACZxi471Ilt4yGEFQhahX71PhWvRulhH1I46hOdFKdyvL9i0kPDgpGxmPdSoBFR6nin8QU6MYyo0iHJ9PSngJL84lrjf'
        'qwyPd8zCbg2ihWCYksMYzO9+PBxbGLbniZzio8hbRgnSMouxxGCkVSvQPvfg+2N/WP/zUsSMMDtKhbWYeAHGMT19tzZ1'
        'nXy7bmN4+cYDitMlHNwit64l+afD62cYzj5////////6ejvXu4GpH8KDAJNLMx3Jas0793/RSyQcBGCFBYJE0nAhEaNN'
        'sg8gFrCqebxGQmcEJO/nixI4QVQAOOBP8sI5dKTOpzv/kp+fEmzy5tZM//NSxEEb2faBH8YYAemeq0SAgIMOXIUInF3f'
        '9JDuGKnJQR3nLtd3K/6P/n//+220TEJdUU1oWX9M83+KAAcWIdXI5PvsslvjKxSGQBIACAmg5IgUFiEceiWOJFqgWJm2'
        'lo0zFf376x3Wv+5lpn659ugbXHjttKYAY7k9JEV1en6weA//81DERyIhuop+C9gIT4pltCNDDKziydy//117UXHlEo7n'
        '6wzbLblQJyqk7v1C4PJTsFhihGq3QMvJ6TmFjQPlDC1CqniETaUrUxZ9nxyaibkn/1skw+3/3ntgZpMT9pkK4DWlyoDf'
        'nlQy969DPDnj/FoCozW2Kzbv/mHv/cB5r/Xf//NSxDMl+0reXsPQvs+3jGq2RRnOXUhZ1jTBPolzZKJ+NAmjv0+t6re7'
        'x98V3XBmjuHYC52RyLwku7/igolZdkA0Gi7Cif///////////X/v/8Leg0G97lnsZCS6TL3J8JZApJiBggBAEIP4ndWH'
        '5Q5RwAm22A0XbVSBIGRJwzPFgMH/81DEER2Twrm2gkrUgE4nU8uB8RF0EUjw1uepEu/em1n93Bv76Vh+usFkLWWoTX/d'
        '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'
        '0XfqaahokWQ9Lds7TVcLP2650O1r2CIsKJkFnb3b6uz/81LExxmRtpW8AkYe4xl9HQoSSVYh13wMs2/fCxoTKUFhHBaU'
        'Go+TaR1MucNTGyRiCed6d5bMmH4mTHFr1TsunIrQZk/9KuJuDOIYPEiS1fRG3LOJVAjodma39faqrS1UdntJLbtuvREq'
        '8lVZzpslTQia2JvJx5mM6vvqcrdut1IjUv/zUsTWGRnmpl5gyvZ+7CRBIkkaUkCjA4TaCACJLCTVSzVqMo4S1wZfJoKI'
        'B1Y9Y0PZhWGPjMYDFbepSwr/0R2spSshlCkAgZHf0l91QCeFCbhLta08ioc7IqeWfKndM7keiRkSIlcsA4ySf8j5KuQ+'
        'SUJesfieZgznlq45Kwcg8Fw5//NQxOcaUzaKfjDFDJMP1Ebq5myyof2GTKGCggToLR0Mvy+WS+Rq1sspGs85qThIoULM'
        'uHo0UBHgmKioYCtYqLP/FRYPGgZFBYWULCoZxQkaircFhcVioqLf+sVFA8aAoVFuKZUKiweNAUU0CtVMQU1FNC4wVVVV'
        'VVVVVVVVVVVVVf/zUsTyGiH+cb4wxShVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVV'
        'VVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVV'
        'VVVV//NQxP8dCZX4EmDM9FVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVV'
        'VVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVQ=='
    ),
    '004.mp3': (  # Make a straight fist, keeping your fingertips straight.
        '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'
    ),
    '005.mp3': (  # Bend at your knuckles and keep your fingers straight.
        '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'
        'rguUNVjK9a0jJE8m5uhbfwSUB4IFggRAGbFyBYwF//NSxO8ZeOKOX0kwAPQcoiIuMNsGqaIIm5oUzheJtZobGVvbttjj'
        'E6DMFQh4rccYzBdIOQQskHLRfdV0UUWVSupaSX///NhZguAVwQQREoEgXx1iyyDkiMuRNOmtI0QTIBpW37oIZ2eKm6+q'
        'AKl/5rlD5O6MFokTGPTHdkFkIPHa+0X/81DE/zgjxs5fjJgDFCXBgyek8i/BTjbZf//7NVqzeBSPh//5z8qRWPBR1QJj'
        'CgK7MX8aMytVE4KgsRJVFQ1gyAQER9oMunm/Je88EwkFBKEwVKoU86p8GjpZ6zoKhqp0SyzGkZ5i9kFO//NPSEg0k8DE'
        '1HGoUFRllGk5OK6XSlEk//NSxJMcuhK7H8YYAHGJINOrVE5JLVyUYjkhCRqZ36KVJf/YqUNNczTiEVVslL5xrpAeKs1E'
        's10TUoiPDoA7nPN5EsZGS6CFIctH3MLKYIafFnnmtpEQaU9bnPC6FHhqKEZkv0+IDl39uUQLHTyJZRRGYJAwWl4RQOUb'
        'nIQq9pKnI4X/81DElhyqRpZ+MMsozNHZHzI07WzlL787H8XdMWzw7fcqK/CQvtLxsU9cod6M7PEMWlFDUd/qPFvbHpYa'
        'KwaPNHEeHcNDdT1IdXFXWm1lQ3enQ4jRezIlst+re20zyYbjSAhQeJ0bVWa5a0EBhB8LV4QkLOpSoymdSlfZUeUqlZGV'
        '//NSxJgaugKKXjBHoMxlMo0p6qdDJVGkU6u7+r1RUK7CXmF3FWZ+sqSGuJIUFjASQVdlGQ0he4YbQk6qeepy78dJzEfP'
        'jt9tyluYiO0bgooAMCoMhwNBwRisVgoFAhgYtrwCwC4VJYGz4IIE8lgAUQRJhJZd4txDxz7r5cNBGhDsmvn/81LEoxva'
        'Bo5fTCgARJo8bGTIqdfyBjQJQYBbcmUUC8klV/HPHUXzEPYJIPcHODbVo0VInCaV/xwkYGpiAIVIWQjEC94bAJ3DL4sC'
        'DzEulIyLyyHEGL1//7GMyQPHZYGHCKpT7Wf94ZCLA0BC5wDKc6e4lrCdTEFNRTQuMFVVVVVVVf/zUMSpJup6Xl+TiABV'
        'VVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVV'
        'VVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVX/81LEggAAA0gBwAAAVVVVVVVVVVVV'
        'VVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVV'
        'VVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVQ=='
    ),
    '006.mp3': (  # Get ready.
        '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'
        'x4NMLLVQd2WUiTbb3BJmB3UlMOh2PtZWrn6PQLfrcIZjtTZ9W5saKqykRQmzIz/8uoYNDiySCzzNjjf/TDafKQ1Mw4lR'
        'KIuKjQqGn3kxRS1HuvEQ//NQxE8Zea6RvhMGFFVEr0oSRUsZbK1/r1uRT4pyI1zSLIFaAodk2bt2137pCh74BAEUKRhK'
        '9YKJzaRZ6dGZpA9s/dAH5LY3PpOI5qs3/u2Si3Ni8d80kd9N1xEqThMMLGgsFBoiStRVNzWuU1aDC3sRXvTpSq3NcNqV'
        'Zav/R9bWkf/zUsReGQlKjb4wzOS5SGPbJpRVCUabc//6VQkYAhAWea1CKwKTH4YEJdyiKh4cvnZBwJrWfRa3FKSZkRp9'
        'EoqB7DgiWVVBM7d6v9Nfdi1VaUcZD4xGMLAyFa2PASkrfnVmQZfTj9wSofYK2dna9tYafkjKnKSxEzYldb62KWc1rtL9'
        '//NSxG8acbZ0fEmGkK63eMiUkLtJuDANY+nwEhajWLKJJgAoeerLgqihJpfJAQlp29c2UvJZSm0WOKIOIgHg2sTl08r7'
        'BjbUuPsFENAxLtcKi/tjAUp4GepP0xWvicxGLuRtfsZq1RB1wMxssiAJrackcckzYScii5FVUcSCkjSJEir/81DEexkp'
        'fom+SYZ0qrI1WAQowrxEoSgEGlPDodBUNEZY8oO4iCriIKrBU94dOg1WdsAIxR5yw152WqDvLeGudUHVnexRXkvzx3yz'
        '8t+mUriXwtuXWYVWZdFhaoV1qzQrRs4qLTVTcVbrFG/ioo01FRbigsa/FG/+sVb2cVFv1irf//NSxIsV8JJxngmGFP/x'
        'UW/rFkxBTUU0LjCqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq'
        'qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqr/81DEqQ5AAeI+CEYAqqqqqqqqqqqq'
        'qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq'
        'qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq'
    ),
    '007.mp3': (  # Practice paused.
        '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'
        '16CpliUMGBGRbm/skkWBRAwLij28GkotvtJN5ggG7TSAK2pijP/zUsRbGdoCeR4wxSylooRGmjhoWQaseiL1Pq0ds1Se'
        '2uY3WSxZL1hKSQlREJcxaNc5fbZ4HHXjKGcEjo3G4pUvVSKkaMakvtmqkTT//JvvYjlUDiBRD8jEB6CrukQu/KuCRW49'
        'oPfrO+d+1Z3b/61IKI0go5DxUVbULC9ZnWRi7NTO//NQxGkVca59vgmGGC/FmfxZn9QrxT/FP9SB//r///4wX///4qpM'
        'QU1FNC4wqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq'
        'qqqqqqqqqqqqqqqqqqqqqqqqqqqqqv/zUsSICtgGNRYIxgKqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq'
        'qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq'
        'qqqqqqqqqqqqqqqqqqqq'
    ),
    '008.mp3': (  # Your results have been cleared.
        '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'
    ),
    '009.mp3': (  # Here are your practice results.
        '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'
        'utaXB0YGu27lBbuzMcyrDrQSsVMaHj5Vji8Y9bzWvvuTECD/81DEmBn6qppfSSgC5+LZYmpk3pxibtGrX+0fCvm09e1Y'
        'GyfyUrX51/lDcsLpUxqr0eBjcPcCFv//51/87zD8GrCzJoiz899ae/OYiiVzXE//t/W1vBeqdlhI9JlxUNYClUkONSsj'
        'QX1lPU6EJUq4Q60/mw6x8WtCfPs11/b/7jBB//NSxKUruyJlm5h4AGZrTXSJjrkJQ9KaSpydx32AXkhh5Yiei8RB2Snc'
        'FrYi5U6VOxF8q7/xF/kVfxL//iLEX/+JXf///+IqTEFNRTQuMKqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq'
        'qqqqqqqqqqqqqqqqqqqqqqqqqqr/81LEbAwgBfpfwBAAqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq'
        'qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq'
        'qqqqqqqqqqqqqqqqqg=='
    ),
    '010.mp3': (  # You're back on the home screen.
        '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'
        'WyTWLjVgluxRI7mqX5skhKh3IGZCFJ4uFnNm/ziRXyfqKwqEjIPLbIhwSkw2hxC8eRY9pA4ow6hFlJVTgiLmRPHWiCxB'
        '12ls1va45FNKvf/zUsS9GamaZPTCRnSXRekV+i/Vf/RFai6aamP2JTC+VyjTyjDIVHhGBqiEQnELClrMtDj4IQPyVl8j'
        'STsvKIc7tsXhIGMxCBD34pr5iFGUJQKvjnhhTwOiHx5BBt7QvHoCoXvFwNRY06bXLvIv+kUZT1oIvj2R7MUA9er/7ExB'
        'TUU0//NQxMwYEMqCXgvMDC4wqke+jkkjjzTYRhVDZLJVgjlM4yQSQ2CkFILbHV3vcFEKij+DO8SUKVhaZHhCEyBCBS5W'
        '+dEwHkSqQGXNljj9JSkkHC5oe9S9xQT0DxWGEi/dq+O1R6HoILopz1j+cq/XTEFNRTQuMFVVVVVVVVVVVVVVVf/zUsTg'
        'GYEmXFR6RlxVVVVVVVVVVVVVRWbctvt2t9Sl82WoCASLQCY1+lVVVUBAV1VSYV9CqGFPSWDolBU6JRhUBDIVOyUGh6wV'
        'W75YO6w0oKA0MDtYblTvPOVLFXYK+s7+DQdiJ/s/+mRqPYi88kxBTUU0LjCqqqqqqqqqqqqqqqqq//NSxOgXuRJs/gpG'
        'FKqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq'
        'qqqqqv+P///+KiqQKKirDCxUVIvWK//itI8VFWGKTEFNRTQuMKqqqqqqqqqqqqqqqqr/81DE4hXoymm+EYaAqqqqqqqq'
        'qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq'
        'qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq//NSxKMGYAFwGABGAqqqqqqqqqqqqqqqqqqq'
        'qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq'
        'qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqo='
    ),
    '011.mp3': (  # Well done. You've finished your set.
        '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'
        'qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqg=='
    ),
    '012.mp3': (  # Your pain rating is saved.
        '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'
    ),
    '013.mp3': (  # Here are your practice tips.
        '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'
    ),
    '014.mp3': (  # Your results are saved.
        '//NQxAAN4AJ4f0EQABr7CAJbeHygIBgo4HwfeD95woCHfrBwEOD/iAEPy5/+UBD/Kf/DAPg+//yjv//9APg+f4Y//1n1'
        'kDomOt2221babOstmsoHOVlNP9uJCIbExgFbnw7YjQY5Khs9FB4kgiUbABkIVpWoQr0yBRN1lS02p7kThf/zUsQ9KaPS'
        'wl+YWAOEy3lzianV9LfFO4OH3utxUuaF0sJg7SYk08ePHF6Ro/7zdZWWpHF2yoxi9eUHEU6p/TquFDRyFPr/8684tC8v'
        '///j+f8/H8f//zdx//xxHFzz9s9LuW+7mP5paGcfX//8c3nLLBioBv1FRNkkkSKgkmqoJMFI//NSxAwc0xLVv804A5GV'
        'w3ws3U6jQeSSCreD8n0MM4nF6GjcoAWL4iAIAADBw0JsCwuzD5pIXFCSjouGo+YXNS7Le3+np7JZP/7s/p///////zPU'
        'nu5U9EY1GZjlHw9UDr9OeXwYf+rYd9Hixf2hH1O/D/zVoJUtum10Ns1dGwg4ZX7/81DEDhpT4t5WbgReqFOUefUzsVF1'
        'tgq02Vd361FcpmQq/hdjqNhiYqFrD+rQKiW7Xqs7DUtiVTuFf/Kh+Uov1+v/qI930c3v+zWYpP////////9/S9XBJras'
        '8jP9////yeitwQnEO5WAAGNxwpKgo2fu6rlgtvcMcaYQCFat7LGV//NSxBke2/bGXspLJrPy1skvX7aYMahNEsh0AG5S'
        'QzNzraM1gWRxKOAgDD6rEAlvw6SJCjjfyFFiXIAospaF9i/H8ggLslpa/N/Iis4q4eW7rIl+v//////0+P9FtRHo7oSy'
        'qrdPunvZG/9Pu3jdKswUg7NcCS5jTcyUBcZWmX6ekw7/81LEEx4Z6sW2y8SyRGrPdCgjGjlK+ZV0QgsTvaufhxoTNrq8'
        'kxzTRIBmABKMS0I0B1HLXuY0jL4d3qHBBhT1FerUkKY1wYE6WbtztSW5zkAjFcEYK67Z///53PNTDobYYDgmgcQ4YeS/'
        '2yx+Cpyh8FX1yEAqW7knzm9QWBQlJpqQC//zUMQQHZnuuZbLCwrCYr5xBqWO/dUrUAb7djUAS6vuAEEiRyvu4VLJkSlq'
        'ECA9hS44Zl6/dy9iNxtCOvnCKgk8kRK3M6v+6qimAUCj6zJ/68qGrErCokPD9TateQsfulcJv//ctAagque0/1uSW87Q'
        'WfIqgJK1CQx7jfd0OoqeaLH/81LEDhnR8qTW0ksKWCToGWMNmgiPgw2uWKSyVUaWOVa48ABBuiw6LP5ATyNuS0S7OHJk'
        '62iKSN6JNpSqKXag10ak3feXxH0f/zffvfK1hQUBxYGxcwUBg2WO////6tZERVSz7/qqiIgUlLZJ+P1WxAkqHyOjBmxG'
        '9UVcOxF2ys3mJf/zUMQcGEHurX7CBQqXZY4eW8KaDlWRjlSxLQ+HdjxrNyUvkBB36UtYo7TFq2OvK3Q/X4n09PQMbg3a'
        'YzaICPS6rnq8rjLux0f7v6P+3bn6v5eGDHWm5b/tua/5tYZr7aOLQipbYSAu20sijXL5wb/xCJK3SQ+jIyewQh0d+T/T'
        'IIT/81LEMBnZ7tI+ws6aDV9glhocYx0INQxl5+l+UMPPPcAwddlOP9P/5hUm56MYyLJNht99dgxHr91fqbdl9272W/fX'
        '/XXAxpA27gANenoJWK14hAIBrHi7bRWSXjC7A+CacTCwa8mybCU9jgdmaEPdEugzVXJejaVdNHyS9zpy7nnv5v/zUsQ+'
        'GkoCyZ553ptFHnES4n61nfU8f/V90/zaJqlzfPO1IB2nU6fLp6pi8ViTKdb+twwCA5/5qsq6dgkHYjUqozxCfrPVI9kH'
        '/VGDf4ErTUjL6kbDVSB01SLg0AMNYsPjb/b+STf6Fr5sFpQjKLhIPm2FamoQVHW9o3NH1Xl1aIQH//NQxEobCh6sAA5Q'
        'EDrwYJaqS3vqKnl8seUBBxRxQB4g5coNHOP3S6nEyFSjnghV5wEoCqTLpiFjW6ZeNj6tL/y8hk8kRog1k///+TokYfWR'
        'z4e5v/j6aZc3zj2GDZkwtjBI8/E+oD4OFUQoiBYCCxOuTrM2oQM49yyBEFDBGjUIIv/zUsRSIktauABoUt3cW26YChIy'
        'kuG0Yre7+3SIBIoKCSlzFpCgxBhiedWEfdMoKYxSKQBADUgcK8fH/B2/d0/yz/SYKugBIrFOIatf////9P/////7/9VH'
        '/7GPy6pZpbV4il01pmLUTghTSNp11VjF2u0gZMs4lNljDxKiXmBRKbnN//NQxD4bg6bIACgTTQoCjBAWAgPJoXKio8xo'
        'ofMnge9rQrVMvynPW4QhOkFzmphGihSNdYA/x9PfdSkLR/dPoh2X/VwMzi9kolqJDoeiFpEKM40xBEJUlNjyNolKXUu5'
        '0Ix0Twz+SrtDO+5LtZlK/dP+jk//r/+rfflKz////zGejf/zUsRFGVMG9nxIxLeiVZM1HQqmUQXeVZyV7v5m/hnPM+Yr'
        'wIO63nuC+j7eruq2J3aR6wLMCGgC0NLORhKg60+r2cn44zSSJjnsABC0jGGBnJOn3xNPu0Prc8BhegiiaeWmLJpRGRjp'
        '2+xD2yENn/fUDDIfSYP/7FpYKEGf//gV35IR//NSxFUYCUrmWIvMNhv71RMDQNA0pJLJ1cwFYhSH6Icz1sKAMX57VE3m'
        'nSqIhcTFCQIE3aU3NMjgxlLVOSYdg4hXFvEb1WNnl9qUQXXZw9YL4hk4RXWWES4nFwHBBUKYR3Jr9z9NNzhEj08Jhyux'
        'fdYrXk+Mmg2XnBMj36Vmmt0tRu3/81DEaiGpusZ43hjEy/6N6/G1d7hoCFAeG2KDtv/6Ndod+unlfJPv1UKWJAGXR7yO'
        '67tnQV4pYdDh+MI1xwuBwAxdVNMtKYNwuKFRjcEMVWFIhD7XjKESJShl44lc1bu3r/D0L8qXQMYCGGAouBYWA4cPNOm2'
        'iv1ERFWu5v/05L9l//NSxFgY0U7m/mvGWLu++y1fR+VZ8jvnquXQAO6Il0u9I+jE1mgWRfKxH5HR9CmCxrHqgCv9gPGj'
        'lDcY9hCH57PeWSoK7kVWDlVj/15v9FzK+5MyZVWrvUivCq7yJuW9EUzjKLIPU2u1+ePWN8rU/7CAovBo24pf///JVbFC'
        'EFJbFLb/81LEahiJ/so+ewSsUc1jHACOL/tHUiJDkA4qgwloQjP7B0W/nloeRsu98BuFVcYbpNVAQRQ2P8/+al7N/zjN'
        'xIZeszNerKQCMwgMDbtO6hQFWGlWMVlpKdkiYGQ/unoV+WPT3Dp0SxLY4QBu1p2yj+FKXQS9MJEWN5FgEKQkD4coB//z'
        'UMR9GPmm3l7DBo5TYFbFBJqZxJIMVGO3DnKJrnKokR0rpNS6N/7q6lmcGNUz1WGmQOIW3/6tVEV1tXpGAz1bmNoWvI9X'
        'v8Ueeey1Ba923TWAAAO/xX27/7gjSHlurW5PX0cTYQ5RNZ4kHHMRAgpM1tSNnpnH4mSpTQ0K2hxK1U7/81LEjhdaKsWe'
        'eYSS57Po9Ven/0PlzZqszFU4USjsQva/+/V7O/5LU/oTznRl/6yN5ksufed2hAwo+f2wDZuDH+T/ah4A4B1/9SLGiFkD'
        'MEMG1RSMD6SEdTNxZ8k3puw7KtvP/n91n/r/Pv/+63yacjIx/V+1qorqiMzsS/zo2us6NP/zUMSmGasKrb55hLBNlqxC'
        'FGCwoouQhFUc4OgiByHEB857VXQofSebgBhuQt9WF//tPQG9B+YKM5FZszuYQGHEjOqMHUQxhJ3ciVZ1f///6SE2/bsy'
        'nGCDT0tr1PcQY7MJi5FUTdRdRdyAIHIEQkXEzChBNmByChVQfFCERahxts7/81LEtBjrnqV0SAttJs84fcQDnFHIxFD4'
        'c6f3qhG0EXJJAocHUpWsxZkzAoeQxjZhzo0zRZkazr37Lz9v/T6f////2P87r/Vt9/dvyMT+wxhWZRyNeO32P0P3RC4+'
        'tHq2PzpMpR5DABBBj6kLyGsniTcHTMeVoxn7tjR+2MYCBznyFf/zUsTGF9v2sYQoC1G7a3Xbf/3hc8pGQCGIUTSOi60s'
        'kQGNHJayfqmg6Huexim+v+aTTgotAzxE992Xzv8ibpCdn52kSEw6ND+WYzhQf9KxxtBgSjutfOOfov0KwJtkoslyJbrS'
        '0/+Z2lGerf6c+/8fMaxCT1mUrmUWL7XgXsIbhiWx//NQxNwZW8LCWiiNPsB3PzAzcmP/Mp4eiwIWeZstv+0XHm42w/Q3'
        'UfqASxI3HInVFpTosauxUi1qHpVPKkiGZrrtbYlC5vsMgwEFUkmYxEcauhzAqGeXCxUwoMCKjaHjFBjVQh7IataDAJm1'
        'Js25rSIjEchIdwNNDoAlr/klh93XT//zUsTrKUtu3lwzDZJC+ERdSklJf9fzQAuMyjQrC5x6ZksDiM0paegvOROU8byh'
        'iWfhb7MMMZZSOw1ylcCKMjSLkbSGsVZfS51KSkry/PcYpNxutDEYq17LQEtD0v+p/8Zqeyo0RUj//v///64rSmBxYoZv'
        'kko+H5LTQ+HRsAXZkgeQ//NQxLspeZLW/OawToBYlXRhYNS4TSB15bFK1Mx+7MaEFN4zYyspCEw9ba/VbGrCgUyIJkzK'
        's3meUKNRNcYsAWuW/EoNMEya9Audd30ECCrlsugiLw2tJIGUw7XnGuERJIVMVlsNSGxSKRSS4mWQ+8KBUiRIoytREiRI'
        'pBIOpUJga//zUsSKLFGOtxzektREFioaCQ8FQ0EiW9sr9lhH5zVrfWQKhAE7A8cGKbsmcmcoNIhvLLqV+BEcrbcd2d/O'
        '3r/HWXZJ+czxpg41j4FmZeFphzJNbGmAhQpUTdZG0grv63ZtBRKF3d/GKABoUDreF0ZTlT8oChj7ONJ6CR9qjtaB4HZK'
        '//NSxE4g62LCXsPK0G31en0Lv93WIlUwsSjTH+a5TKzU1dWtTVH202619fmfpKykiNjKWzB1TCsRJZofgquyhT7Q0sAB'
        'kSc21v/Wv26YBNaz39Ao602W93qOMZVzZ/l75NW9eZcJSqaSwXz2B7+0Ol6ntojCWN2KrbCPbzs7Tp8JD8r/81DEQBuC'
        'ArWewwbUwy5oAqUNxSq8/h8KyJsR5tLiRTbkWFSf7E+sN6iKh1mpaNnG1NDUiJipZ939jMAC8PjS7vDEdAMXHfhH80sl'
        'vbHfxL4vq0fe/5/nO6Zha2DO0OFjbm4b/X2PlOMYRyLU5zVJROSNqSVNoG0DeQijnsFJzwjJ//NSxEcqw+apTHpHPddG'
        'GCTJycjboLmhRFGkSYugQMEiNdGUYRhcTjAGIoxWTqk6RUNyQQKAW3aTEF31qjpX1M9+lHaEEIL+i+mHGd3Fu+j5ZGhG'
        'RoiABf8REAEJCrm8QANKaejmifm72CKBnPh4/kf8H58ph+f9/ryF///+TznSJdv/81DEEh3TzsQACZGp5u6z/XlGeRWi'
        'SbChYGAiNoFAabHk70uhm1ErgHZ07fbPZMmPBQC8RxQiZLfrogUoXfNPf0hMiB008JQ1hSQbnwnSC4wgiqFC7IEoRsKC'
        'J9Uwp25Aj2iE5d8ClPZhf1zcaGbtOnmq//uv22wAbcrUNNQIuhqH//NSxA8b2+cSXjgNizlq0L31nfR6c1q6sqdX0b/+'
        'f9f//7PVTjxM92SdJVyhFIdlM2P9jMdfhnXL07tl9+enD4XEVbEHi0Sz+UcgjoKYGAyYhHVXqWKVtQUXJp02gnLPolYG'
        'YTnEgI2A/COI7VV5mFd3eH/0eVuCaiVi4SGJqedrRZr/81LEFRnTJvsaWEVu6Th9bSrahHqrbR5tHae1pqoeuTqbai23'
        '1FhO/Cbu7mrRy/82y5dOohD2X//T0Uu6qiwXtXb17ZHootpXY5FNJcG7KfVhZGtSJQjE5RbeUapTehVZlmZoh3/AEGx6'
        'DhE9A6hIRhdEwNDU2oHa0k0jFTpmOtuyTv/zUMQjGYu+8xpoC4p1FS0a2SN0Dc479Bb3bTot///qX3/kX5P3uxKO4xhQ'
        'QYDkGFcUEhw1ysg1VZyDBLmqY4073KsjQ4ZHaUyjC1KOw5Z0qlmZeIiYj/ZwDn7aMiGzmClGz11KigjNPwbUjYrIk3lE'
        'aUW0aTLaBVGpHG5rz8X1LX7/81LEMReS2v8cSE1aUpHyJn+KQS5f5c//upSfFf/luz//bvu5RWEyQdA00F2XEllP5Yoe'
        'ffWAj4x66lh3Z3d4f/ZQz842D1vPnMsJJKNyt+T51tf+tPeqNs1J2r3/1/+WySYojZiREGv//9///+v/+tP09Ks5RUBi'
        'h8WChAVEAKKHMv/zUsRIFxt68xowSzfdnR3PbqzfR1JqrjNTfgA/xcr+erUf7Z3iH/EHFmEwQOB8wkdSuZBQOnKpnU8a'
        'OLQp2W5U30dXd2plXte////6vrt//Vi2aem3pMpSmEzDxEFFhITKHAgHxruxEdUGNSzJf5c2UTZ0Y7Oc9yjhVtA30hE9'
        'VWHX//NQxGEW+67qeCgLxn1cg+BfUERIvQ04xELKWQfWy6xRMHJnBB+q9RbPuf4fRdn1IwHrCeNj60P+U+r+9mzmI7Q+'
        'KllgVu2wXmldttal/FoiFngt26w0RUDSxcRCdtZ06d+InkmcSgqGlPbXGle2u1sQvwMgFWFOCrKBJjB6hiMT8v/zUsR6'
        'GPlO5nwCTAqqxjiBxj4qGFj5iQgWBroM/FDN6VrzSKU14+pvST2OFG8bkus+tZ835lBhemc6T4wLIomDGJArmXq/r6S9'
        'VNJOvava3dXfTV+/+LXO2b9fW38j82HJTvVtBaVyKEmH/vl2AEOYCPRv+fcWWDwxqCYQ2VLLIZVu//NQxIwbIUreWAaw'
        'GjSEgV+ajG21pMVIdX61VtJNf5108AsI6PFZswR3V1iuopIykNaaz2KJ+QpprLLQNresDH+5v5b6mPU1xwNLU7KE8r//'
        '//7/+umRtaUCCkt6axmDJFw4YzCXzw1/XDaHgTF9f9vDSB/RYD3EAci1r/MNjVUTVP/zUsSUGnHSzlrTzvLFAOW8wat0'
        'FACRZmKAgEJllO7+ccT6uX8v0K3UOBfV288vncv//////////suRjgDQZ3PSo7zyYF/K9vdp1IDSWU8b/tqRJjnFpp8U'
        'RYOcSsSHSikG7BZbvDsLYcZ04xqhCraScTyK/1Qxv+YLXiZMmURbNu2L//NSxKAZw1rbFnnFKFHS4h1lW7FEwkwImhTU'
        'homUNnv///7XaGS4KMaERi0DdG7SidfurYUQAzdoSCYFN8yZjG4TXHxmQnve+1XE6nzlWR4q1SY3WomN4KH8dmb+5FCM'
        'i+MDWEigRN4NukTo9K06VtS+eyNdElMbZPUj2Ml/////////81DErxfxOs5keI0I/7t6mTg/cGNyIKkgEws2ncyK5G1W'
        'NaIwBDWJaAF0ObvTTCRtufjgPoTCUjPiYPxJeX4zsb2XgcZedpQeUJ5w6LLLMtOxu3O5wQJTGd0mPJs792yMulHUzXBs'
        '9jL6GNUj3////////95Xtu7lQiRLGSZ8XLxT//NSxMQZM0LXFnjE+P9dwrNZ/fSquCM4loAVA5v8qcynKVXjcUNnhzqF'
        '6iPIne3q9noj4S1j2yYVDKakZUk5xf/rbICDhggYQ+olkIK54I58+HMp+4yqwkFhMo1yVP///+LPLGpYmLA8TAYinTqr'
        'Hnysr0IJosJoaK2gABFimgXdS7b/81DE1RmLFtseYMUIUFqcnw6U6ixThxMx8qIdSpk3pCgNF0zUjrRNIsuky+7b6Wj/'
        '2//ffT75KYGlZw4yCxvSLxisfm523O85G/tPyu6CWlCVpLIgqR//u12BINf0SQoIluGoB5R8sDZgjYGrfTadzEXtBugZ'
        'QX/wUpNPQu4ZwICQ//NSxOMZKa7R3nmGjAhwE2hLpIPJkbnebJhIIlbl59db//2l30xN2w90Ftn45yeyes1lJ2B9v3j4'
        '6HMJQRHU6B0CNEojFqpKdhXLmjJajRsyWmQSM4XGchIwhgViUEkWdXlq6qEE/8q1VQifDqRoSDpVpY87/nmg09CRa3aN'
        'Jy63TiX/81LE9BvBtr52S8woPTw6K6MZDgpQCuthJswUVpDY6emlXKQ43GYCBJD/lMYt9m1bmYznZSlQ4MAqCwrHCK6t'
        '6M/q3uxVXCpyWZFmeUVEh6/+fdBYRGi3ufZ+iIQk8WCsOtBU6JQVcBu1S86Ig0S/CDpMQU3Qe/bZvX//zKGwQRqN1f/z'
        'UMT7HvnGkG7LBrzEcJWFz/Hf4gJI2iJXIAw5nK+/Cv+UdcNS7CjW0+MXN1/QPO5xW4TFUHCxn9SXazoZTCSnFZWQe4YH'
        'kH983R67qQipVv5vpturUTblR8n0LS/49GMGOsRQoqY6rLU7eUUZTEFNRTQuMKqqYCcu21k3//8y79H/81LE9Btxwr2+'
        'YVMWNDRUyHkRNxkpndHNKkQgCrqiK7nTW2pa3fZ52kGOz967t2LFyDyFMERXX45av99CsNElMUIjhLVHIiIVH3smUY6r'
        'HPWVi+oZ3ixppwIuMv049gKGqGpLVrtanyi7JTFDF7aW21opmhiwW2n9pGQBGpBGNKHQpv/zUMT5G8L6xb5hitKTLmvI'
        'BCUCy9wSVJwiLLSHTmXyScotfteco4j9huWVv2sxSZQMh91GQ3j8qHwmDuHw/JomuUvQmBRziRw8Uh8kNGPMB0PywCWp'
        'Qnu0iyakOc9mnfOKCVZO5ebTWh5t/2uart3t97mPqkxBTUU0LjCqqqoA+y3/81LE9hsyCsZeYYqysdt2+2UA6yWONi4t'
        'TJOIgNKIKDTK3najTw/JLekro+4gFSpPkoZChZ7PeEroDUSWKESBHeoKCk6LBOYFUMP7XosuQx73emKaGCyULYsYSkwK'
        'wGUw45KevKWorFPFvgd1WpdMQU1FVQD5bKg3ZHLg1YZrbPq6cf/zUsT/HvE2WADWWETp4Nx5fVKArVZqRnP0JfbYxytg'
        'ux0IviUGp00YQy27/3Dpt5TIDC04dNjMg+HCYgEAwzHiEBqKB5LWAeJ72pQkiiKCAu0yQqLvAZjr1E1GErDxdE4YJhhv'
        'pZqy+17kuV1xCoSAS3bVZXHLv+nEjUyQ3g9ETjgs//NQxO8ZOSqJvgpGHDY1FgphMjCMYiZrlCXLPEfsPpGc3BhZSxiK'
        'gFhtuCHCas4kpuGU2uFmNhSZ0pA4obDcFECHE7JoKUXkux9qxUuSWL6YS2/a9JeMtw4tnuM9m3vOXFzh2xFvLSlJc4ta'
        'kx3bi63NoYzOZCufLQwWAMFuMBQKi//zUsT6HClCgb4LDBAMi6xcdWYDAQwaAaktyCrCqMohQogCDkUOz78NvzWGnnYx'
        'OGozZcSsCrCdmmpsRNUVezWEp22W/wmI2QqkKVREssKOAVJJEUbKkwDGMXThiIZC8WaqmzDEcl6TKpyr6ghReedqnnwm'
        'UnQdSzNfYv2kbzRjP+dK//NSxP8uC+J+XjPHGeuKCjzA9TbFPD0YsAtjrO2yCq6xnJ1US1atTlrGu9I77gKrfP7pTKJB'
        'YAB30r3tjHGUtYYKtUQEOQgY55joIqSRDS4oXILkIIT6Dl40SC+47zW1ZmYIokXIGRcgg/E+5kxICtigdJMzTFACyBwO'
        'o+aGaExMibP/81DEvBnCBoG/RhgAAyQQHeUCIB8YfOMmSyazNNBSSk3Qpm5mYMaDLjJiFAsYAYAH6B1haeKr2++ne+3a'
        'K3JMLgxS5gFwYgmVxZZPxmyf/////zcZgnDQZQgjIjnkTNDpuXG///////kHIufFzjjNyfdA4RQqOYMckyRJJZJbJrU4'
        '//NSxMowg/59nY+IAJQAAI6Zg5l+VSQZGq+FAAXh6knErDcUNeu4UZ9advYT9i/dL2VUqtV2MSQs3pe+rYT0FeeyRIbd'
        'HgyKU6U6rI87djwn39oNcz493xzZNgf4UOaVyy3YYjBkUyv3/6Rvrxy3CFIapEKewmaRmfPtvWpxZqabVbv/81DEfi/b'
        'dppdj3gAtj/7xPn4///nTre27UqUguLNLBgPMojOPCzp9Wus4ti2M4+fn/dP9/7YYx7QTmVzEhSvUz5tfQ2He6/GIU4h'
        '3I1KWu9gAK/w8EMQHprEkj9BCTpJGlMayPY8onphaqjY51omZndBxaipSTBJI44bW38a7pY5//NSxDMfIjZs9cZAAIy/'
        'rqOLFRcOQowPBcGglEwDQ5EFZFwqNEG2b1EVFH3QwYUJ36qlhrhm1k1QVUDQdLLDqNLNseGkrtKgESqDvZAwa1IWZEcf'
        'f/6KErb+32tBlu2SjXzU4RDaafRxQ1ImEJHST/XCa8oECM6mXKdAQl0D41K0pDz/81LELBjZ9opeCYYci855arrEnP/5'
        'w2gWHmOYhQoY8+//fOxQFyC1PW82pYh9mJKUEmEncrLi1c9ShSmO3Te7bR0ZIhUWZn8fVHxMFZYVmKz1cJ0UREZRnVcZ'
        'ha2dyNlM3/45LGEXsEqwH8sU87LNuLzLNbC6RRbdh1mEUWZAs2KSvv/zUMQ+GYHiWEBg0ywslGEBETzrPfq4/2yxh0NK'
        'Gv0VStldzC1D9y86zcKUeOq3di/v3xfogIAUkkzBltsXOWSaqqq2qKCtYkSJb//pd+M3GOlG1ARK+xsxwCMiUs3qBp3Z'
        'lj2Iga/lgaPA0Ij3zxJYa1nUdnrzv9vVBoGj31nesFf/81LETROY/mZeCYY0w0pMQU1FNC4wqqqqqqqqqqqqqqqqqqqq'
        'qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq'
        'qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqg=='
    ),
    '015.mp3': (  # Left hand selected.
        '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'
        '0iAIORym0MZZv8xtF21oZfl///1p5v1aah/oKe0RXpzsNHQVdYnHO7YNxtyWOoApOf+zhIPAgXVJUnNGhEquWjnbWIpw'
        'sQWsJ4mgEMQuZ9nj//NSxJIac1LOX8kQAriWY9gqDhDEgjzlfM9lm//fMzhSGYgqFLrzZgI0MPoGDq3J+zln24lsfiE6'
        's6elZFZYkezqPX6XkSK1ehUDqS7b0A3ffvzWLbTaMEEWsiYHc2l2m2qTfS+e+rNMp3eEnP+HsZRxFHHq1QbkSj0VW7Tf'
        '9v0epkz/81LEnhk6BqJeSMTySAg5cs/ugoGgq4gdf8dfb0iQ2utwcO0pUeD2qlr4QWeXUx4xb5Vdwur45eBUZHJADJH7'
        '5xhpAqevCrRSvFZIFSJOT41ktkKsi2mIcFERemhBwyQlj8Uy3h5RAbQrXMyf//8s/KkiD5VpYNdNfyq1/lMUwwcwdP/z'
        'UMSvGOHiib4wh2iSPjwshHHoAu76pR3Wu6BU42i7NMV7uscqO/dtttbttH/2Rh604I1hEJqwuKD2yxujaVo3KPZgtZ8+'
        'oq1uShlIEeWknW6tK3uzfl5vljS2TVIv+eSjfzrLEKTjX/7//o5ltUBk5hMQrHlTXBtT2igmF9rPM4f/81LEwBjKAnW+'
        'SNEUdBLWiGt7UUU31UxBTUU0LjBVVVVVVVVVVVVVVVVVVYASm3Ld2rdsTmieJhmhSJycwow+TCaFCEJCQn5o0TCi/DJi'
        'IQoV9+TiZhRC+NQEYMKgd+ehR93/3Pu/+d+1v///5VVMQU1FNC4wVVVVVVVVVVVVVVVVVf/zUMTSGUoOnb5ITYZVVVVV'
        'VVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVV'
        'VVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVX/81LEzBCRtmpeCEbcVVVVVVVVVVVVVVVV'
        'VVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVV'
        'VVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVQ=='
    ),
    '016.mp3': (  # Right hand selected.
        '//NQxAAMGAKA/hjGAi1uclkktg/iO0gJ6nYPy4Pgh09/lHLP+U5zKAgCAJ1h///L+o4Ud/6///d+71v/w+qFAhOW7bb7'
        'bqMb0ZQEAwmgOgmbnNfYIxWiYC5+5OCHBH2BDzD8D6bgmNGqIKKZfGEvrqZ51CM43dCQtTEGbMnnk+tKFP/zUsREGdHq'
        'rl5JhuKflSPLPCLNKNPaw3EkUW8lStilvdo937OrppT+xCrWpTUCOiqB3/JuW6PYdlEngEz54BDGrtsxYLVQpuN0MC4B'
        'HBNsGZD3PDRhASXHjwsPNdMwzgOjFAiMGAJOcxiQDlmYOaGYwuGwoDDAQoMJEM0egTDY8NKm//NSxFIqIWKBHtcM0NAQ'
        '+DhKZLP5lMTrqEYBMFhkMDxkMmixPAQIsPoux0UH3eXXKn8sgPbPJlhZ6eHtO3abdsBBhB/EH7P6UyHxULlBPP3fWqf6'
        'qidn/sbn1uPr//43puV5SgIKrbbbbaLR8qL1bChBMXAVdx4KhSBkk1OkhDfUDff/81DEHyBKAu5eVgyeGnaj4Jqqv5FZ'
        'I/ROZ1nnjD+ozCNpxKrHUmETkwFBIOl7sxRX76VezdIlWrHKOXXgYgoA8mdARAaJNtQL2H0AIQQxsJjCabRzEP4iPvey'
        'GdvexjEEIjxGWTo////yf+J3+k5VHYAJ220Wj5UWPIQuCz4kgXv5//NSxBId0hr5nlPTLhN0f1f/0dxKYhI4ySFqOPrc'
        'VjZ2JlhFjL4ZbOfxLg2SoFwWHI/S2G+09zYp2SBAfEyZBFs0MhkLCwrE6JVAQMJFCVJUnRkhlK29e+LL2tLwXRFBHzTi'
        'emGP///7Ui9cbDCwsLCiVbUCFkAZBOhliRUh0z7/yNP/81LEEB0MCuY2C8QWaI/8U5TmifgQ2oMBb0Mr5Sv3UpmfQUJF'
        '8wMWdWKRCMq/sm9MiIYxTHHFAQCGIDBwaKe13qtCoR0MqMq/////////73pWhAjg3KjCykJOruquxN1W/iwco7CmGRgE'
        'IUHVB26hhKqsEwKIoyqk6/FaoqYxY/+TKf/zUMQRHHn22lZmEC5qTQk7r34YJDk3XVxYOB+fBa87cFP/am8czldTwwtX'
        '2SDUHhEphuWEH/s/xaiR66GMKrk3OcnDQSM+Znt9rFhcyhUNHk+jq/Fv/etSRjB5GJRodHCpbF3b8C2iU7UHbQ1V7ACa'
        'jE7lxqPS47wVQvY+pGosAsb/81LEFBxh9r4ueZCc1IK5A4c0s75CXfUtVkco5fbX0tSPx9dKpmmeS1dNPEoyqcgFx14t'
        '01/8NXfErxx/w0rAsdtxLWSObOgPBIBf9/0KR6xFoNjTwaOHgXMgYCjQaeDVtM71hgSwVo52lcAQS4nEh6UxK2Z6lHD/'
        'Wz4tyOz8SNxlTf/zUMQYH3LeulZ40xzxu7bTe6+7wbySQERkFA+6FGW7E5mcI5lx4zCyRi8s9zhaJ6md30yJEcvvpwwg'
        'zizhOUI3HCE5Ofl6KAmFHViM4q03OaNJjggQgABilCAGP/fh5wr+cGGy7j8mhkQHA+yUKO/gRyGxVx3S2NgxS55iBE1T'
        'jBP/81LEDxnpjsJeCkYcUCJ+LmtQszdD2hUcpPFHILbTAXQlUZjgQ6switrYlCZoRIEY5I4u5hCfTzzn1Qp5s00OiKIo'
        'dIrQxI9x3IjAZSShMAuKiFBJdU62eq30lTLiyzTCMgHf8RJ20S/cBck/zq7YWwRZC7Kln4FjRWk3MGpiFZ0oHf/zUsQd'
        'GboCrjZ6RkxziqDUhG0zzJQJs3hZBp8NCJkKM8JtThuJyJSMsu5fvudJhyJljzciRHz6roCA0SkeTbyxKvHWpQlq1Dlq'
        'i4KCwdLPU0mnU7/GWRJWi+llOSw0l6cOeUH2zQAhWWbYFOQDEX3cOH/1hSPxh9S81Ot3WOaNgmO5//NQxCwZ4Wa+NgaG'
        'HhhDxxqUmCMKZ247WiwQuU+1Qkoo+ehuEYAEQWSJHNERtTLMmJaGg6CJ4iY2f/up686sNM+Cqej+pTv5pf/fUbzWJ77r'
        'KwEAty6swjYXYTJVDHkh063gg0HwPqiwZlZyG3MTfqZ14KUvGvrZytpSOPvtmdn42//zUsQ5GXmipADDBthHdYojUrhE'
        'UlZ4zNz4/9f9JymO8zL07xUKuEBETidgPjihyc3LQz//////fECoAE+AkCX+kEcj/8qzahZwSd7qCqkK3pFqi71IJpFq'
        'UFUzxn8f8+nktcygAEzqOG0lScu551cwYSzmGy33P96dPdkU5JRAkymI//NQxEkZ426+LnmE9PnTX/Yuqslzf///////'
        '//9U2Y7SI6K9GHi263/rqqohAfAGVCn/MwAZt2wVwxY+3gvs70PGkTB+xYnNjqSDxjRq6Jruc0e6kyBj2Dw45CAC1Rh3'
        'aaggI0MFirUfm6ty6tuV6CVBcTCxzDInAxRjCQiKhwY1xP/zUsRWGdG6uZZ7CwKkf////reIyoQfQIvz3/JQE+qVUNwr'
        'c/IParcNaTUgdaDnRYLJByyu2HHxGzFeLRwMXLDJGEABWgPVx1ajaxgXCVjqtjrd9HjqAuJUdtztDc3Ly9xPElw41C9y'
        '0cq5u5cz/JbKZ/169f////8srSBWuKKwIUVo//NSxGQaO27BtnnE9lOJLUPXsDzkY/dZqpaKfgyByDA8OGm4ogrqebOA'
        'XEbQME0cpola9mc8E43ymz2m91VjFtBDXuhfOZXJdWuwjEAsGYcv4lJSe31jFYYMOIlUQUrCDq0rbvjJG5HYhA2O7///'
        'osIxrga/1Fm45G3Nf9x/AeAtVWv/81DEcRj6Apg2wkq2SnKYS2bJMmmICtTsJ5Hc3H7g4ZRorKgsu7vQhhIgeEhocs7i'
        'SGeaJFaqWYVAxxURc9/djehcntzPjQ6aPVqb0MVucqIsRoqGt93v59P6a/83/+vRy9XtxvZfv6xOCAAbulu/lksv/t7E'
        'AQrBCnhCE7fdDrL2//NSxIIac5q9v08oArM3EqNNWGph+Hqj4jk0nBiqmIRYaHy5chWHDcdySRoO0+9xsi1EknTAmEo8'
        '8oHeSasnmFm5pCKRqkv7Kg25UOEpU6Qrv6qGVKZ80QYbvPrX290yipH///85oOw4bn3s83Pw72w98LG7R//////80ZRu'
        'bnx2DsP/81LEji4z7qJfmFgAhPe8mHGbabJ5hubsNiyR8QLP/////////4r///N0h8JY67E5YTyHaXSQolgx4UCogZjG'
        'Mrb///////////////6bsqqtTWdlV05cZJAwdNOgpSkNBAmz7KppmBdGbTK6jNEzL7qMidJIwLYoMsEQEBBCgzAW4P/z'
        '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'
        'HjpG1l56S2LlGCWlxLqysbsUIxDM7f2koaqjOyzIMwhBjCNN//SkrYMMiI6LjAuDYdLsV66f+zkj9jyCgk93MY3QL3yR'
        'XALxYkE10CktZTjksuGGF0GYdD4LVRnCcqypWBmoqV9W2oPIEjqctQuZVj3k6/fHsy/ztxnaiQ8z//NQxJ8a4hLSXnmE'
        'frvX3KoGBgM63/6lmVlailFqkKIsIzxFPNIJuIyKGPBqSo//9fq0EaREeEX/0Lc1PoyShU1YL033H/VglS1vn8CpmTwC'
        '4jvM9gaHRQxENsaSGkVQXyiK3khQypqewI/gYM4vGCtspR2btRVYMf///ZdmvPnrXP/zUsSoGSm2tb55itJMHCDneKnX'
        'ISSP5WAgkK01kdDlUDKt5LXVDTjY8XQapUtqAmHVjA0nJdrLtttx/yBER8LCZ0kTBOyVQIKSYo+Typ2uZOR5Mw2MSurm'
        'Rh/xfRZolKCycferPjY1GM+/e/FOU3zaFrB3AVT1KYkTyF6Fn0qOO1xo//NSxLkaQaqJHsGGjLrpS5ELNmIoyjTvaFn0'
        'q5Yg5ou5AhoV2avbb7W9vySSRpIY5xAeeyJmyL1YWbTpMWX4L0+0TzCEk0PPvmBEGwcZgAcYl9/dqC/Vpdts59anZFEn'
        'dhoRHRJB/Mahn37O9RQ8SNREBAjQNxHbK7sG7331N7aF9Hr/81DExhlhmrZeSgcOmM6OdbUFZS7Ta77a/3q6FQkTnp0a'
        'RQmuqxGtWm5nG15bmASoiMRMqqdCT5SpNRChYsNS7vASKz0s7Zr2+67nruqdWr5ER3lSRyCSJZ4wNJqrbYSsF0O71GRZ'
        'nb1kLYQRucnQO6ddqkxBTUWqIFdts2u32unp//NSxNUZGhKBHjDLLHOnH7EiEXbe1Bls40gR0uwjYdeyR6PKOMDhAgSV'
        'H1/ZlYsC+lcy4h1pC6RebwjMpmxHEXzMIfvzQz/vvCyuRqX/LS6hGoIyp4UCrHpCIUfa6DgVd1mallRUWepbNnMozvvr'
        'TEFNRaqqqhU8klJTGTagSi+B1yD/81DE5hhaEoG+SMUMTgCj4AMFScGqkoSgtoo7k0k0o6Vg4mYYmpWClhijlUk3Jrsb'
        'b2b/kbVSZm4wEwUBwmdFQWBoBA0BXCYSnQaPCICrOvK+WEusBP+46VI+Pd9T50Sz2WrOksiWH52Gg7FRkrVMQU1FNC4w'
        'VVVVVVVVVVVVVVVV//NSxPQawlJ9vgpGHFVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVV'
        'VVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVV'
        'VVVVVVX/81LE+BuZZjw2Yga0VVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVV'
        'VVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVQ=='
    ),
    '017.mp3': (  # English selected.
        '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'
    ),
}


# Prompt TH fonts (SIL OFL 1.1, see fonts/OFL.txt), zlib + base64. Written to
# fonts/ on start-up when the files are missing, so copying only main.py works.
EMBEDDED_FONTS = {
    'PromptTH-Light.ttf': (156316, '8cacd868d26c83871bf144fc70899364645984bb821a97a3f14293157d878112', (
        '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'
        '+EpQzbwGWL0bKZofgVAIO4fyyb1X3aSq5PK4NCWnFB50KsaDkyNbTh9omp9OviDhAvUFsgvAs6GCJ0nNT0OsAf+PPmFR624n3jIN'
        'ZHpLz252QetuN/n0pPICCDXwbhkC4w1eASO916tuUVVzBZxRyWnzH8cjm33cFTCktO6VLZCj1lY05v+mwL96VA8edsQcxEfBS+Yi'
        '0RfMqyPfw+fvRr4fyaDRGFXwrxz+3TcyQD/vhcgMyXNmH15Df3cQL6HPSb0NqIExQr2vMn8dqRu5beQN+oYban6V+XnEKj6hcKQL'
        '/yahzehtXIpvwv9kljN/AR/kOvYgeK9Wy9yyZ+SZ8gXyO+S/KKoVVyg+U05Q3qv8WlWt2qp6TZ2uXqFhNT2avZovtHna1dq92uGE'
        'uoQlCXckfJPoSVyeuC9JlzSQnJH8cEpSyikpN6X8UZevG9Tt0ev0NfrN+r+nzkx9JC05bX3a4bSfDfWGTYbnjNhoNE4zrjXeazxs'
        '/MXUaFppusX0NIBoT5+Tfnf6kQxDRkPG2oztGY9lHDWrzA3m080+87uZsszSzDMyb8l8PUueNS7r7KxHs36w5IKf9KVsc/aF2R+D'
        'T/Qu8HpeYO+yf+mY69jnTHJuch53TXE97y5y78vpyrk/ZyR3Qe67edPzbs17K1+bvyz/gfyfCqYU/Kbgn55ez07Pz4VzC18oWlX0'
        'bvG44ntLUkuWlewr+aA0odRbekvpS6XDZTlls8quKjta7ihfXP5CRXHFM5V5lVdVvlulq1pV5asaqe6p3lljqtlR89a4pHGnjnum'
        '1lbbVLuy9t7ar8e3jT9//P3j36zDdePqttW9Ui+rr6q/tP6TBlVDc8OFDS81qhqXNL7jneU91rS+mW1+u2V3q6v15jZz2z0Tcton'
        'TWyaeGhS26Q9kxsmXz15uGN9p6rzninjphzsGuh6pOvHqZOn3tVd33199z+mTZr26PSq6TfNkM1YNOPhmSkzz5/52az2We+dMvOU'
        'P81+pee73uW9b88ZP+fGvtS+VX3vzO2Ze9Xcn0696NSReRv7df3XDagGxg9sGHh9UDfYN3jzoG/wrfmq+ZXzB+ffPX9kyDG0aOhP'
        'CxQLVix4bKFuYePCixbet/DjRcwi06LaRX2Lzlv0wKL3F+sXVyw+dfE9S5RLxi/ZsOTppbKlbUuvWfrxaQWnLT3t0LLkZQPLnl1u'
        'Wr56+VsrWlfcu3LHqomrHludvHpg9Zunu0+//PSf1sxb89nalWtfXJe67sx1X50x74x3zsw585wzXz3zu7NsZ8056/KzXl6ftL5x'
        '/XXrfzp7wdnfntNzzlPnes696dx/bGjecP6G1zYaNl6/8dh53ef97ry/nO84f/H5T10gv6D7gocvdF/4zEXFF9120Z8vLrx4+8Xv'
        'byrfdN2m7zYv3fz1JZWXnHnJa5eWXXrzpU9e+uUW+5YFW57d8u/L7JctvezFrflbd27Tbjt92+uXT7789ct/vKLsirVXPHHFv69c'
        'duXB7TO237H9+PbhHZU7Zu/YuOPAVcarFl/1xtWJV6+7eu81zms2Xqu7du21R6/ruO7z6xuvv+UG7Q033Fh94+U3oZuGbtp3c9nN'
        'Z9387S1Vt5x3y4+/WXEre+t5t/71tlNue/C2X27vuiP1jnl3vHRn/Z377hz+bdNvr78r+a7+ux6669u7XXcvuPupu4d/1/+7N3Zq'
        'dl688w/35N0z754H7vnbvR33XnXvO/dl3Tf+vnPuO7SL2zV914O7Dt1fff9V9+99IPWB2x/c/ODPvz/x0OW+3+4+e49tz9w95+x5'
        'fG/C3oa9l+39ZO/wwwsefuLhfz6if2T6I/c88t6jjkfPfPT6R4cf637svsf+8viDT9ifuP7JRU++v2/jU6qndj71x6e+ejrh6bKn'
        'Vzx90dOvP/3LM4XPXPDMb5/5cf+s/Wv2b9n/xP4/7v/22Yxn25+94tk3n/3bc6nPVT8357mtzz353JHnvjkgO2A5UH2g+8DSA1sP'
        '7Dqw/8CRA399PvF5z/PNz/c8v+L5z18452DjwQdfVNJ/j72U/NLgy/jl9a8kvLLhla9erXv17lf/8VrDa7//w5w//OF14+ttr1/6'
        '+kuvj7zR/caNb+x+48dDqkOFh1oODRx64NBbh75+U/5m5Zttbw6+edGbr/xx2mH14dLDg4fPOrz98O8Pv3j4k8P/PJJwxHKk7siU'
        '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'
        'Qb8pNZQUeijMfIBL1pj6TphcFIf1osEwpOJ3pQiJITiSFehy1Oft4defldL1ZyXZ1sTQWBWldB06Jp4mk6ncVFZcRPA08KEqWXEW'
        'omNjelf0VeiCMHwjF59j4stKNK4CYsdAi0gjUCJ1HUzM0pUmImMpwcABV/T5R4IYafKEVAPviqeDS6jmh53SkhF1FL1Pg0iijo0J'
        'wWZJoEh0/VlExz4bsepTNbDwriVzi8kkxIBh0WrYtEbbh3fngihkYqJFbcjmSHfk8vvVQDzDk6i5peAwq85ZXycmUrNknH0uhQmS'
        'lTSu26ouqhByqWXXGFRbzwjCF+TMM4KtD14pss2eReQ8CLKtDvzmJ2/xS/2IVUJHI9BH4V5BIznkwushB1yY4KCLrRKTn/+msLHM'
        'Qc+/MDp+eT/23K2Hwg+e0NFjOSLlDfoO4CL0G1XcEK9wDG6P3luKg1IRv6OIMiKeByrnfVnBbbXCRmSdsLteDxsJHWXTv/7zdP/X'
        'k2Dj4G5mKqROoL9n9wf2HYMPmKVZBRg+PTr1QcCOQHHfsZ7+D9uBWUfZtAceaLjvgWl/7Nx1XydU+Aps6XuZqYGtfeOHD4oxDPtp'
        '300m1lKiCg5jDNmmS3cdS7fP6qhDhe+1MmlbjBX6qf8UaYt0w26MNslMWE9yH9I8ZVoVJFYJSaQvbPYMbngkW3eF7NN0HhzSOH6X'
        'nwL7Pw9pn0/mEgYBK0DAz4GdZFS3Z2WwirBTpeAoBCJKSj6/E+kTTgdJMZppDkn1ookT+h8K4vowQ3v49RDuRMn/Egr4f8YtYxg0'
        'F8DY7Z8/Grcw7CpBzO00qgayuECDbOSmcGiF+GIxS2vHtPr6X3oPvdn7C1b1fvxRL16EZ/m/xOn++/0343z/O2Kf2AD1KkmeDDmL'
        '2PBeAbWSXiHUCkvPJf4Zh49M93fBObN7/NfhZf4u/w+CPDEbKFW0xNOoVkD6gChbzYUU+joh+w+RX32gbuLoYoT6gQ5+h6QJsQUi'
        'sYI/GaMENVhRoRLLbzTnc6jodGIeDkFag01V8ZJ6sdgakdGQ9lihPV4+rSSbicVsoucqkVQGsKGJyie/IZj3K9OjzrKzwCkvkUxV'
        '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'
        'PQpRJVSYawX1pGSuhaie/NVzrZRfPdfCM4ezwidbAqTVkLvBDvYB5KjKSIP+D2HJqeQYSCU5g5snNs3jMBQjj4PDAekmShywlgjV'
        '2Jy54UC7c+BcLGFKTPI5poWnOyWk/3Dl+PErJtcvMMtKb9/oacqoTSkqO715ZXdjy7pJ5VMKCruKOvv7O5Nql7S2LakpLbxl8qTK'
        'WodC3qRuKa90LXx3aFtbbUlXYclUz7wpnf28dXic7EWGOwP4c7Z4VRnp+kQY0sl+WOJrLOITVJIRgehglk3vENNT0vmwKTSFoxnS'
        'AIZltISEbQpwMcJr8I5C1h/4uRzWWw1GI8TOuYxOSyZn4NJS9JIUz2hUhjIHW2bW+pdTtjavzZzSYV3ZNmtJqu60tspTyspOqWTx'
        '7uGrG9dO6VjnHVeOB4az+ivHNbTVb6xvL+kZXzu7WODsZpDBDLDM4OQIS5YRzFwlCW1lWBJsISOxfphknBOlMWIl0GyGXXp5ZpLJ'
        'GYZGmptA79ZS6y44++ePJaaZLuJJ5uHDU8aPjymdv6nbsKFu+O1o3oAlgZ5USPJSh/WlsJTUQp8KyUttt5NeZS+0w2wnpG9pxtS3'
        'pDOh2P2ME/1vcfrbiyH+t40BvFyk54XjxadVi4MWQcrlhH3WUpTUY0KJ5JSIjQo9ayoeHuvHiZqjCEbhNHBDQNYX8NBgHY2eJN5S'
        'Il6DIdAHtIUBjoQ0ZBoyAWY4ndSeKuTd4YkcavHqeVPw4DWbziHmbCd3+qBgzoIlO3suk3TJ+jO3SkxW3mDlZz1MEbW70mEABumH'
        'tVJYz6BxpoLRRVIukt3svA0vdl1hFBH6fEYGx2VYM6zQhdM5kx2CPiVZ2uMAjKeQ455iQU1tsfiQk/gyB5z4Anv+IFZKBjFTciYQ'
        'U6bmc2HA6iR4olWyQNZu2oMVfRq+7zqdJIjMme/Mz3UnOhLtWbDXJBA8lhAreCw6Pv8IxImtiomUJDosPm7EBskE7GZ5pxNbE1Zq'
        'uXQaeyyameC8g+FGyQ0K9qZCIbVEBKdeVpZCkeXIctiyFZkKM2GNTvQ0V4/Gnst5y7M7Ji689RkdjWh4EGsqiEfAkAoggk4CD50Y'
        '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'
    )),
    'PromptTH-Regular.ttf': (163248, '14a4c0d15f21d832c7997940ca77654abecc8f6ddb47919364770f822ca70f91', (
        'eNrsvXd8E0f6ODyzu+pykWQVW7asYslNMu6mGCxXik1vNqa4gOkllAQIENITQoD0cumV3JFEJJfeSCf1LsldegKkkEraXQqXWH6f'
        'md2VVtUmuft9vn+8IeNdrVYzT5tnnnnmmWcQRgjp4A+H0sc2NbcYlur+gpiOl+Fp09gpk6dPHv726YiZk45Q1udjp89sMKd9cyli'
        '1v+CkPL+ydOHlc8ffdHpCOEr4f2u3pXda5af3bIPoRQoyvbek9fbZaXVvyLkvAa+/3PfmsUr6+6y3YqQiUNI89Hi7nVr4Hk6tPcM'
        'XJWLV2zq61zxmRehwi6E/2Vbsqh7oZX19kD92fB99RJ4IH9Ktgk+z4DPeUtWrt8o/6bmCfgM8Gj+umJ1b/fDP1e/hZBrHEJyy8ru'
        'jWu4+dpb4PuN8L59VffKRTXXd1+MmOzt8PPNa1avWx/IVt+EGP9vCFmeXbN20Zq6gc3fIeT4HN7fjwhtMGpo+ef3Zy9Iq/0RsSx5'
        'jl6fVUvaR59Z9tn6bwzu4d7nRsJHBWIQ/x8hZ0NwDkIyVf+NAy3c+7QmyX/M38gTVoPa4VeFcM+gEjQGnQJf3aL5CD5jxDJteA+S'
        'wbs7mHZ43spf8XxUjutJHTKhLgdpGYVbaGxqtSM/SvmVYb4ZkKODXAO+zY7xJbRdC/MioQRigWI+/G/4GXACr4VvvkS+/2Vhr+YL'
        'cz6qZ56Da7zyBHz3FsqMuJJSLZRRkjJcuDYjGzMm6rtEJR/Ky9BOovIIfP93aJdchYK+gOsi1IC+JmXgEPp54Em4PgLlBXhWy5eB'
        'f8PVBdc3oQShPIA3oEx8CtR1HfyeFGeCUoRa6HUWSmP9qJ4U5q7BCzsS6Pl7ynwo3XFKvHdPBZp0QntQ2DK4Xw33iQr5PllZi2rZ'
        'Gri2Ak0SlYdQ7YkWtgXKuNgS930ih18I5VtUKt4z76MS5lG4kvIUKg3dR5dlccqIIZbhoXsbU5XgnUvjP2df5gt8X8+44BqvkN+e'
        'BO8Ng+vNwmdSuuKUBaF7FzMvwTtRBXcDfy6V1Btd2gG2+fAOuQoF/QfK52IZ+AD9NHAArg9DOYh+pc/+Bd858eP0/h/wPgfX+9F/'
        '4J3voXw9cB/gX09LDbzzGV/wvXD9ZWAAL4Qr6X+fD7yNvhx4G9cOfMb2gqz2hmEAftqkMMWUrQC7WHajOlqkz8RyDqqO+HwrlL1x'
        'SvR7F6BRnFngHV98eDfgQMpDSIt3DxzD18D9n6DcBLod5DFZYTaBHBN+nMzrF3w/lE1QyOfrUQa9bqJ8qD3h8iqU1+KUDuH78ZJ3'
        'J4CslccWZint44MW/K/YwswEuCcB/LfD54+gPI7Kmbuh3kr4bh7Q7iGQ1+1wT8olwlW8j1PYlVBOg3IMytfwrAXKRCjjoEyGchrU'
        'ScqZUG4W+s16uF8rXKGwn8BvoXCp8GwFlBKAa0DAww9lOYXNxyyW9K1VUM4U6t0D5RT4fBZcSfkRuVg14EFkdLdQunldgm9BaXjv'
        'gI5eCY0K4btikIsJMEaXDPxKrrSv3QDfkXaboYyB0gF0A31N63FA3XP4e/TrwHkM0JEB3FkTXF+CcgjK51D6ofwI5WOo60J4l8jX'
        'TCgdUNqAB+QK+gSPQS68RLiP9147XFdJ3iO4nw7lZCivAfxXwXWDUHaiTLZB0Bevwbt/hfIu1PkQXFVwPQhXI3wHsoVe4wvzK/89'
        'w/IFT4PPAf49/AGUz+DzR3zBswGG2XAto8UF9PJBsYnfs2baP33MHXAPuGOADT/MX5nZfMHrhXJ1uCCgFZhXtLBjgdaAP7ca3p8F'
        '9+kok5p8xIYSbRuXMF5MEsY+Ild3oQImZeA2YmfgrwQZATy4b+A3YCswO/jn9LvHBJm3QPEI9CEw1kPRQrHzhTXA8zvgt8Jn/CCU'
        'S6lu4N87D5WwG1CpTCXgehXlfz2VCSKTcqjDI7lOgdIG7xHYLxb6VoIrsR/RAShPwm93QZHB80/hWhMuFHciL5vh8yi43guw5gl4'
        'WQQ+ttPx14fQwHQozyIULIMCNvsA2NQDzUJZCmUnPE/h74OT4LqPf3+gA4oFylVQ7hDeXSLyC/r7ufD5digPCYXcv0kKkTkM8oD/'
        'BqVcuO4HWF7l5RG/AeUiKGlQQG7xmwTO4P7+zwbmDvQEbwu+038kmBt8qP+m4A8D7uDfg0eDaUFf/1PBN4OpMC8gJY0vA7oBXfCd'
        '4FtwnTEwc8Ax4AyeH7wgOC9oDlqD1v5/9h+F613BuwbmQq25wR+Cfw/fBQ/3fwctdAcNxICHwkLJgL+YXjllE1zfRtuRHGYTKWgY'
        'GoG2ob/ibXg3vhjfiAP4ffwZHmCsTA0zlelgHmWeYF5mPmA5Vsta2Ty2gC1hy9hL2TvYR9kDqSNTJ6d2pHba0mwOm9tWbBtlG2/r'
        'ta22nW3bbbvEdoXtOttxu8Kebjfas+w2u9PusZfaK+wj7U32NfZN9tPs59t32W+032K/3b7Pfo/9PvvD9sccaofBYXbYHU6Hx1Hi'
        'mOGY77jEyTjTnHqn0ZnltDmLneOcXc5F7hvc97ofcD/mftL9nPvFn97+OePnvJ8rfxn4lRkYAAxTYNZSikaiG9D9FLMb8N34FXwU'
        '/wfmNDxmjzCPM88xb7OIlQNmLtYTgRlOrUudkjrHprXZbXm2Ilu1rcE2x7bCtt22y3YxxewGipnebrFn2+0Us3L7CIrZevtW+3b7'
        'hRSz2+x/se8HzB6KwWy6o9Oxh2KmA8wyQ5gtBMzucd/vftR9gGL21s/pP9t/LgXM8MDAwI+gO57gZ24Dqegl6Swx+H3w0gGT9MnA'
        'ZQO7Bi4cOG/gnKApyIBcHCNP//U8SvDfRx8eCcLfto/K4W8FfYI/av1o9UcpR+47cu2RaxE6cuaR2448cOQR+BeATzdCuf3wJ0d2'
        'HDkdvtl4pOHIqsN7D0NvPHzK4dXwF2agh6cfHnvYcRh63Pufie28/8T7j2pdmq81RzRvqi6S30JlE/oY+gFvBquGCG0JW8qWs1PY'
        'aexc/jfsXHY+28WuYE9mt8VCzm5kv4RZtJJTc+mcnsvgTJydK+H8XAs3hZtG3uCm0L+An4yRySN/zf0W8enffIn9j/uI/v2EL8Kz'
        'D0nhDnMfhZ9JAWMKmBKmiJnDbGYuZYYxI5iRjIPZwngYGKuZMsbNlDLrmFXMasYLNggHo08ucqNiNBrm981oAvTROWguWoQWozVo'
        'B9qJLkSXouvQregx9Dh6Gj2DXgFpdjLDmeuYcuYgeh0dQ9+gf6P/YC1OwRk4E+fjIuzD1Xg4bsBz8Xy8APfhNXgj3oMvwpfjK/AN'
        'TBVzEVPNLGNmMIXMbKYPesZi5mLmKugbl+PbmSZmA9PIXMG8yPyJ2cqkMenMk8xljIt5hknFe5lm3I//g4OMDxnBwZCCrMgA41s2'
        'cqLhyAu6pQpNR21oMpqCPGg12oJOQuvReWgzjCbngDa/Dd2B/oyeRReAFfAxegO9h75ER8DC/wp9jxVg8Qcxhx3Yim04F/2I6/Ek'
        '3Ihb8BzcxqzA7fhMvAlvwVvxlXgejLpmdBQ02j+QBSx+O/oWZtc/oDz0L3B3fIfy0U+oAP2MRlKr4TdUjWVoFFaDD6UfrKV0VIdT'
        'USPWowasQ+OwGbWAtTAbe9BMnIcmgi9pFnajqTgLtWIX6gArqxMXYy+ah0vQAlyK5uNhqAvsh4W4Ci3BI9AyXIuW4lF4JFqJ69DZ'
        'YGGsxU3oLDwLnY870S7chfbgHrQbZkiX4cXoSrwMXYGXosvBGroRr0M3gGVwPVhPj4LF/xDeiW6H0fARvAs9iC9AD4NFdQA8M8/B'
        'yPw8ehXfiP6Ob0Z/gx6zDU9B9+CzkRa9iybhHLQON6O9+FR0Fz4d/QVvQ/vwaehOvB35YWzKApssB+ZB54JNdhXYhTfh9cxDzIPM'
        'Y6Drn2WeZg4wD4NmfAT0/lPM86D7X2JeYV5gbmNuZ+5g7mTuYv7C3MrcwtzN7GP2Mn/Gd+HH8OP4SfwUaNfX8d/xP/ET+AB+ET+C'
        '78MP4Dfw8/hl/BJ+Bj8L+vc5/Co+iN/G78AY8wE+hD+E0eYF/B7+G96P38T34tfw0/hd/BY+jI/gj/EnzDT8OfMq/hQfZQ4zHzGf'
        'MEeZb5nvmWPMTPwF/hIfw1/jr/BnoMs/YP7OvM78k3mbeZf5nDnETGYmgW1SiH5BReg4asIGNB5b0FhsQt0wbvfgCtSLK1EfrkHL'
        '8Wi0AmzRVdiPLsK96GKYI16CF6Gr8Qr0J7wS3Qy20S0wb3oKX4aewBejJ8FeOghzr9fA5s4AG9GEPkGp6H3wSX6IdOgQ0qPDKA19'
        'AB62fyIVegupYaTVoHeQErRbDZajEViJarEGRqYBmLthVIEZVIlZVAYKcAZ2omnYjk7FE9FWPBltwGPRKXg82gg26Saw70/G49Bp'
        'eCo6HU9HZ4BH80ywq7eDfXs3PgPtx2ehe8E2uQ+fB+Pd+egBvAPG9HPRi/ha9ALMF1/C16GX8fVMHTOGGc34mfHMBGYccz1zA5PH'
        'jGJq8R1MLzOfWcR0MWcxpzNnMGcy25mTmeXMacx6Zg1zHrOTOZ+5EDyKu5gLmN0B5LUH0Mz25g67vfVBlDq1NSCfPqc9UGkNFHR0'
        '9dl3zGwPMO7uh5SAdm+vq8fqcARQRwA1upruAU3f2NXgC2BvwN7V5wswXvtCe+DAlADnmXNPAVY3Nvc2B+TN7Y4A6+6Y1tnucDms'
        'O9rtgSlT4JG/w2oPDCd3wzs67Pv5t7sXBgrgkfDJHigl35eSNw9MabcDNDu67QH1lPYueGIn36nJXTW5q+6ydnV0dFgDuLijwxVA'
        'U9oXdXT4AqzXDvVw7m6ATNY4pT0gczUE5K4GwKMjgLt8Ac7rArjsC/fLehrs5BsCsZWHgPwNcF3NvQG2yAFfNtp32HdAA/tLZW5A'
        'cmp71xRr97SOdleHo8Me8E9vh++sBDWhfV9A5g0oGovvAduNUkoOH10NLqC4q6E7wPT0BXAvQBGQFfkCCq+dgKpp7H2QQz12UkPA'
        '39VBXulqoqAqvfcoNKixuaHIEaK9yhvJCzVfCy4GEAB2d5e9eYerm/CF0gtZCU0DdisAKUIJ3HF1N/FNaBL8PJAHv0LWMGrSH2m9'
        'FKF7NGoWmG11OTqKHL5Ainc/wzQHFnY3+QKpXnjRbg9oGyeQn8ONq6EjkEI+TYNPKfDJF0iDatIpSexAgV5oN5Da2GXf0WUPpALR'
        'fIF0b+uM9v3cwqaOvEDKItdGX0DnbZ3a3jqdf2h1wHMDfa737kdpjTPb96elNQZwd0MgrZjILEhyw34t+ZMCfwLYBJxg3VPa9xPi'
        'AbYNO4C/pNkihwt+Jt5b+e/JT6ArkCcdgMlYgH8sPI1kVQIG7kfI4AJqNQbQmHswxpRXBi+sMzDNM9oDaa4Ge3NAA8KndoHANdi7'
        'oPn70tMxKKSGhh1d+/Xy4sCGYqsTyJQBuBmKfQGjdz8mVxPQmVzN3v0suVq8+zlyzfTul5Frlne/nFyt3v0Kcs327leSa453v4pc'
        'C70uke4BeRdQ2GUvCeB5pIP4AkWSL02hL0/ivyyWfOkJfbmW/9LmRYGU4t+BXy7gZwO47IAfuToAP3J1An7k6gL8yDUP8CNXN+BH'
        'rh7Aj1zzAT9yLQD8yNXrtddSMfV5odn0Lnsj8LarkbISup6XyGqJN+ArDvigFw6DDjDWnoCLru7hLqIRk75hJdiXhliLTYFhRftl'
        '2NjcDoqMIFgmpUzs1+VeexWFtwLew82xjUDvjNs4eY5Mf6WWatMY1/D95dgIGFUC/gBwfHihU3QP9wWqvCXmWl+gerBXQYB74fUa'
        'YAkyue0l9rGk4wMpx+/YMdY1FjRFO4wQoFhBG1RjbMyA9oeDhjJB54L/6SsBVWPxoh0lLru9dgfUNSL8tb2EryPAQZ3wlj3QRXSF'
        'f2r7vYydtVvvZTxsVkcD0Z9KUMUu+rarBXpuY3Q37CI6jB8umMauha4A29i9EL5mGrutcN9F9Ff0b7oBJNDqrhbgoQtaaAG84EJb'
        'gfriNOLiNSUHygFoLwOBksXUCjUSjNwUCPg7hdeQ4baA5SMJDWDeGZB5BBq4aoE0o+jjgBI6j93e4hpLGiPcqqUkIwgIFEUz2kvs'
        'tTC6EoiFh3YCi0hyuRs+jZcO5Dyj4kmwwBkXEePRAgSNImu6yEgfjaLIyjGgD0oI1VpAqdd2lOwvwRnQAetCj6dIH/sj3477Tr03'
        'MLw4bqUN3sCI4h3QMBEWgDb2HWBLSaAEXm0MSZhIXSJcLhD1EugkfHVNoDRA//8OURz735I+Aj7RL7UuUCESfjs6BBibCTFE/FsI'
        '/g6XQAABjxDKYwFlI985wTKAfmgoCVRCXxyX4Pl40Lk4wxCogvsJ3kANXFoJ1ZqBrvYWGAZFOrV5iTgGWuF2ovce0DNwMwluMLmZ'
        '7L0H0ydT4IY+mUreaYabaeQdcjOdvENuZpB3yM1M8k493Mwi75Cb2eQdctNO3iE3HeSdRriZQ94hN53kHXIzl7xDbuaRd1rgZj55'
        'h9wsIO+Qmy7yDrnpJu80wE0PeYfc9JJ3yM1C8g65WeQNjAyRuY98CIyBu8X0rg7ullB5gg9++LDUGxgVensZ+UDfXk7vyNsr6B15'
        'daU3UBt6dRX5QF9dTe/Iq2voHXn1JG9gdOjVteQDfXUdvSOvrqd35NUN3ntVHCMaXg3FAeWiAJs3ZaM4pvhI/MCD6OA0sHLwLlDN'
        'vAZYsx8pGu5rg/AMDhWRe7+6XlXFFXJGJacUHrQpRoGTI1dOH2gaHkvfnrJdvV22HTwbKniS1vAYxBrw/+gTFjXtz8PnTQWZPq99'
        'P7uwab+HfHpYuR1CDfzn9YLxBq+Akd7hVzeqarhizqzktEUP4oGzA9yFMKQ03StbKEdNTWjI/y2Gf1PQFFitR8xL+DB4ydwk+oJ5'
        'ceB7+PztwPcDWTQaoxn+ETjvGOiin+8dmCV9zjyC19LfPYuX0Od98G8qmsqYod4Xme8GageuG3iFvuGBml9k/jNgF59QODKFfxPA'
        'F/ImrsB/wr/AbOsndgS7lf2aG8fdL6uXPSQ3y7vkf5L/oqhUnKN4X3mO8guVT7VF9apar+5RP6Qp0Zyj+URr1s7R3qj9JKUkZWXK'
        'VSl/T81OnZt6TZo2rTft9fT56W/oSnQbdA/qvtWP05+mf9VQYphhuDnDkLEh421jufEa48+mXFOP6WkzMvvNs8x7zPvNRy3plpGW'
        'rZZ9lncs/8kcnbkg8/LMw1lpWdOyNmftyzqY9a3VZB1tXWu91fpJtiZ7RPbC7NuzX8kO5tTkLM65PecT8JfOtN1p+3fu2Nw77Sr7'
        'IvsxR7fjc+cFrjzXVa5f8lrzDrht7h0e5FnhOZ6/M//zgtqCGwszCncXvlukK5pQdEfRF8VVxecV/8Pr9e7xfuAr9e32/VRyaslH'
        'w/zD7iw1l64qPVB6qCylzF92ddnTZcfLXeVTy3eWv1dhq+ipeKKyoPKBqtyq86perVZWL6q+rfrHmkk11w5PG37u8BdHyEZMH/HX'
        'keaRNSMXjrx25IejRo5aN+r6Uc+M+rG2pPb02gO1v432jt42+s0xeMyIMRvHPF6H6nrqXvPfXT+6oa7h5cbNTb6mW5qtzZ+0rBs7'
        'apx7fPb4Oyd4JlzWmte6sfVoW0/bTxMvn1Q86eHJsyd/M6VkypYpr0+tn3rF1B+mnTft5+l7ZjTO+G3m3pk/zZo22zh70+wP2i/s'
        'UHU8NGdHZ3PnU3OL51409+t5S+Y9Pb94gWzBmAV7uy7qTu/e3ePqub03p/f0hXjho4uaFr286Lc+fV9l33V9L/b9tHjE4u2Lb1r8'
        '6ZK2JauWPLZUsXTy0i1Ln1hmWLZ12Y3L3lzuXD5t+TXLf14xecUTK1Urp6y8dhVeVblq/ap7V/26esTqc1e/tiZnTeeaJ09iTpp6'
        '0v61qrXda/vXrVyvXP/sho4NB092nLz65EOnVJ1y9UbFxuUbv9t06qbXN9s3n775+1MXn/rNFv+Wy7d8vjV9a9PW7Vvv2fr9tlHb'
        'Vm175rT80y7enrX97O1HT591+tNnWM9YesZtZ/xw5ugz3zor96wLzzpydtHZC86+8Zwx55x3zuvnVp9763mjz9t3vvX8xeffsUOz'
        'Y+aOuy5Iv2DpBR/v7N15585vLqy/cO+u9F2lu+btumLXO7urdq/effnu9/dU7rniIv1Fp1z03sUVF991ybBL5lxyySX/uDTr0rmX'
        '3nvpj5c9ebn28imXL7/85sufvfzzK3xXnHHFG1eOvHLzlUeuclx16VXHrr76T7o/bfvTV9c8eK3u2lXX/nJd4Pq91/96w8obXrlx'
        'zk36m9bf7Lv5kpt/veXWW9tuK7jt89vn3P7kXuPehXvvv2PTHQf+PP0v+r98ui9/3/J9B+7cdOfzd5numnHXzrtevNt598K7nwtU'
        'BtYEPt9ftn/X/qfv0d0z+5799/x8b+29W+/9070f/LX6r8v++vB9pvuG33fDfb/en3P/1geUD3zzYO9Dkx/67pH8R4KP3vbokUcH'
        'Hqt9bOdjjz2ufHzu46c+/tET1U+sfWLPE68dcB6YfuC6Az88qX9y05OvPOV8asnT+U8fembas7nPXvbcuc8bn//tYP7BMQd7D553'
        '8B8Hv36h5oW+F6544csXtS/2vvjEi++/+MNLjpdGvDTzpTNeuvulX14e83LXy2e8fOvLB1/+5ZWCV+pfmfPKuld2vnLrK4+/8tYr'
        'v7xqedX3av2rPa9uf/W6V//66ouvfvS3K/9e9NqC115+vYv8eyPlje43bvuH+R/n/ePYPx940/XmxjdffyvvrVVvffj20+9UvrPt'
        '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'
        'O1k4rF4jsaMtGraesdqPtHf5brik/Zf2Hu+Df+wBPsiH+DA/m+/B6UqjfIyP8wl+Dp/kU3yaz/C9fB8/l+/n5/Hz+af4BfxCfhH/'
        'NP8Mvxjnol3KLxNeBrSfap/FvtgA7RAsFr8J68QgaEG3wWLRgj2nwVo1ziv8LLxbnaWtgR2ar2bln+NXaPdr38PZkldpgfxqfo12'
        't/Yt7VHtiPYz7QHtsPag9pD2OL8WZw9dx7/Av8i/xL/Mv8Kv1y7lN2iPwLbyq/xG7Q7+Nf51fhP/BjzU38JvhWeTy+A17zbtTq2H'
        'f1P7Pr8dcjRJ+4r2Re0meKf9sna79nftH9rnta/CYvIJWD5+SfuadlC7kR/kd/A7+V38bu0H/Fv8EL+Hf5vfC2+R9/Hv8u/x+7Vd'
        'sLpMgWXl57SrtCv5A9rl2tXwWHmYPwjZfLH2GH8InpZ/wH/IH4bX1Uf4o/wI/zH/CX+M/5Q/zn/Gn+A/57/gR/mT/Jf8Kf4r/jR/'
        'hj/Lf82f48f4b/jz/AXtGu132qva/2gvwerzFfR5v9d+q/1Bm9Ve5i/yl/jL/Lf8d/wVeK7+H/57/gf+Kn+N/5H/if+Zv86P8zf4'
        'X/hf+d/4m/wt/jb/O/8HP8H/yd/h7/J/8ff4v/n7/AP+IT/JP+KnuIPPmYTLZzh7gPcccfq3l8nb5GOymHxNVpOfyR9nrwWagkzB'
        'phBz1e7J/r39XjNjwwV1VXXyXl2i7jZ1L1T3InGHd5RaFb9I3WvUXaWrKlP3KnVXcKoKvapGe3onx8e8qsYHx8f691iqJofHBnt6'
        'Z6b7varq6O5b0zs82TszOjDSf66lpm98uqe3t39s2lzb24OEuE2O90xLeDaVr63OXEfFMNdRJIWtKk2NwqpGYVGjSlNTZKlzgldJ'
        'FOLVVV51CtE6iagKrzGvoxx817mQtK7rHR8d7ZFwLOvmgSy0eazf3TOpXqp817sSqrAi3rDB3OCsBpC3XiGoyFdT5tWgsGmQ2Jgb'
        'podH+vp9NxiwaDRgYW4iUpqbCFlrk+GTRxMQlHDtijB2VWq7yq+o0Nws0zfL9M2G9CqKqvmiElPd2KB6LjO3GEpRWyCDaxXZa1Uu'
        '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'
    )),
    'PromptTH-SemiBold.ttf': (169652, '3dd6e74b2de5e5a8d5dbad90db85e5e78254bd20127d482d855f3bc64772e039', (
        'eNrsvQl8G8X5P/zMrm7JhyRbPmTLkmXJji3bie8kTqLYTgJxQkLCYcchseOchJCQcIQz4SyEo9yEQrnKDQWFo4WmHOVqOQqUttyU'
        'o7SlLVAoPX5tsfx+Z3ZXWsmS7bR9P//fexDGu5JmZ55rnnnmmWeeJUZETvwxUP6Cnnnz3Zuc95B08vn4tmfB0iXLLzmrdiM+v0RU'
        'MHXB8sO7ivI+v5Kki78msnxvyfLGptXGKy4kYntRf3B4y9C2zefOv5coB8XSN3zi8X5TV0eIqPJ6/H73+m0btsy5z3cbkcdAZP9o'
        'w9CObfg+H+3vxtWy4ZiT1zsOv99L1LiTJMfVG9cNrfXmHf5btF+G39s24gvTy8ab8PkwfK7auOX4neX/yOWf/wftPXTM1uEhec1Z'
        'zxAFDyJyTN0ytHObYZXjBvy+E/X9xw5tWbf79c1PkdSZj8fv3LZ1x/GxMtstJA0+QlT87Lbt67bNGT3lC6LAJ6i/jzhtGHU5m5ov'
        'WJ3X+VeSZf49vXbEujf49XfF9/pGVsRPNjYaDsVHM0niCf4MGbriK4iMS0dWjIaNjer3if+kV/g3sp368NQU3EtUQx10EqeS/SN8'
        'ZiRLR0h9ZETdPbgS9SpXtoqa2FwS3Sn/BZTbRA/dPb1+ilLOvyTp81ET/cTQxW73M3aF6LdYeoFTgmT2FwqgEDOINkk2kH9SRVav'
        'jMom/QwvV6DsJb90FbVID+PKy33qVStP4Lf3yJty5aVRLdPV0oRSitJGrZJ79MdSM+5bdL+nl9nqNYTyJPrJVp7H739Bv/yqFsZw'
        'PY9aQSeU0V8yNno7rnegPK18J77/GNdSXH+B8neU/exscrCzyCE9hud5KVFLoe6el2IKiWv76IjcTS28SI9kKY8n7+Va0DO9VCSu'
        'hRl/5+X4LCVT3VNBk+PQH4pcg/vduM9WOvD7eOVcapTbcT2E8rKWH1PjgRbAnrFkrMvl8EOU31FQX6TPAde7KB/hfryyAXXSy8ET'
        'lKXqtUu9No++lvguvVyrXg9J/V5+Rin4vUUCj0XxqtdS9cqfPQnlfZS71M+8rNSVDVQrraMp0mLcD1O1NHv0F9LatDpZCjsOsnyt'
        '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'
        'XnqUUHsZbPR+IXbv5qoiHI6ng42SCtYiM1jpgMZ+4ImRSmDTEo5+3tYEghfp1fHgGqueucNSnnEcR9mqZEZCekZuFltkLWG6XjbI'
        'Rvc90Yxt2fI/lkzZpevbExLayjssFZWWzeVtCQntFR1F5auKtnxSUpKZCddEOZx0XLCqpd5orGtelVtSnFPeUmsw1H6tJDOrtDQr'
        'swTr5RYaDOyaDDWTI62sWBYWEgj1kJOdpo8K1/iA5UQik3NgLsacj6jQiTP4/d4uW43ppabYyJiIEHboZnQ607pGW925JxKdGiP7'
        'MO7BuWfkO6V9KR19XZt7Ng6uq2tqrF6bec72QUtM/NGYuCAaFTqU4/vHzK6GBlvQ9i3q5J1pPr9LLF1jbekKOoc+FmVNSAu2P1sc'
        'nxZ8O1rSVtPD9K8gxTKgAK8y6ewnJSXCXgXYyuivEkec5YONiy/hCw1aKUAbsJ27vvLzE3qEQNCPqrfq2LmPrhPJzWdLBVYdMZhU'
        'AxtENRo969S8JHLFh73OHfMTgUhLYDvCc7KzMuMz4tMNerYrHBelw9ODNPFKhZXLKyH3blqs9OLBPE78ZryyYmJN8Zbku+46bLHc'
        'mLapdGNDSFAjOvH4Jfm7PSK4fLypcaIyKWFw97p1u+f+VGTUT5qzt2ZZmlatanxotziPeS9MSHLgDOO2MFjyCgd7iAyilTIJHBy3'
        'xo+Ja/BwgEcXiK1P4O4Kln+YRQMcyK7VOjfMCrfeRkNKRGgoDN4jQsPYZlnYEAvlYGwOj2KXl0G22M5aKzyEwQss5+Z9z9BURkhZ'
        'k+F7k5Xn5mZ1LD+v8PrjhBy/3nT+yi352d2rg6d22QJiY3S2XfsSkm4wJG626WJiA2wdSWmHUsC60HELeEeJgRPqk+Gsi7BQkDBh'
        '7OgCtFHVSD7Ok+rZxm2sYTUeTcBOfYhjFgvc0CdVg500jGfATVH3QlG4LQv4p8Uz6MON7KhLdUYJliYcJpEl6KhBg0vwGpiPqaCE'
        'dSkxscZck39bQ0RjcNR5XWWG6ARDVqF/4PkRF2yOmuh/O/i8oIxscmN/vW0bHFCfnrO8395l24rcfwu9A5pvJFjkp0gVFSthtw0l'
        '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'
        'OEL6/wAqOXem'
    )),
    'PromptTH-Bold.ttf': (173160, 'ef40cd87803109d67ff697d8f03727056b18a68ab77c8abe8eff335e669d392f', (
        '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'
        'UsdwdoajcHbH3OmHb1uSnfPlg/l5BdNv5t/t7Gxfn9cQFbFodsXG4k4euDAn+WbXb1Nzc7PuJcXpdn4zKBsDyuKc+OTYKASnCAkK'
        'DPDTbNKVzHskT4wVI7lvARf9n0Y6NGlWqFjeQDijUBoAotnC9fvq6/etP7y2pmbthoU1bYdnzZs3yz9w422trbdtDNqwPij3IafV'
        'NWgre7AgaD3fE9FSN78lkiT5nbCe1yIUAM6XD/A3i81XNrBfXIxYcJduae6VuVWeuV5kema00JSiaeTR0TJ2PiD3Ufu2be131+Um'
        'N+VXLF48b0N9fv3d/qF7urquCFu3LiB+X3T0nNlzZhVem2BbR6gc4/tMIdBP7q4ID0IILhOLD4ZXUEZagsnXx6SOLE6TittmERXR'
        '19ypH8aQvEgP6uLZoZ0qA+NNmrIixZMIAWDGSyNOO4gIi0zPgBe32A9KVtoyETFHhM0x1rqU/CgQCKkMoabSWhfeeGnSvrgwe+K+'
        'vPD8zXUdbe3t87uKi4YXBUbtT0oIzdg/sP6GA9+Nv2gB81m8K+Ch9OSLN7VcnJL5YGoym7MswK+D1P5kXsUDsYyZJVzVgoNsfsCT'
        'a/C6CadYcvWBiJe9IB7xt+aLmFvGY6XjuFjQzErIzMrLEeuzZQJxocxTwJ9o4aMnTANiNLEYdYbYpri4FQvWOObNczQvWB4bu2Lh'
        'mpI5c0rWflxcnJ6Oz655uY7igrnN8+32utVz80qcOfPW1CUn1x0uTs9wODLSi6ktb+d2MHmeYKvY6AisXMSJY/WmCSVT+NiNCeEs'
        'Z/9JGYmZiq08Q5wKR60zmUQzSsajBpe95FyfXDrsLMyPKSprWb1+6eH66tXN+aXxRaXzG9PXrD1s840KvS8hITEhKiE2Omdz/YLO'
        'iLa1fsl3FSQlCl03sbyhfElHWAu5/M7m9/E/gurihLfXK4LDYCXMjMM+ByxN+pvUOW+FNgtkMRMHtIl4kbHCYEoxUGFXgDOOXMJd'
        'pFmtAc1aQEBCgM6OJZPkoxz+/uQlZvfKW1FkzGbVAqwB6yfNLc7iroBDoNjAJ6IUoTYIdBgONTo0EEdEskhx8rRxF3e0indoMjIy'
        'w/yV31fycHWncNAabChekXTjjUePqggf2RVBrh+yf7os/ODecx8Vzps32LBouCIhrnnvkiWua9JyKsrK5uWkuc5eTas+Z/gWTHZy'
        'cWT0CnGiUDjcNbIYlvAYjs+rhxLsL0IS0LkMKlIF4mdBzgjfiTiihb7vVcUsT0tNiQgNxWpuRGiY2POKfa2ogWBuXEo9oQvF6rxY'
        'RsHF3TlZwoP2Oidjzjr7Q8NVm6ZPWz2zLe+q+xi7b29ux6zmwoK2BcG7e7v9w8L9u7deEp/0UEpibTdOJ/Hrnp+U/qA9AfvUv4Lo'
        'Ken8HUQWG6oIC4V6EyaOZqDd9RZN7IEqIFVH7MFG88QuMtPRC+JIC4oPIZ2Q0i00qkMPQgyjtomSSFcbhDATQztcTsUZn+asMqpN'
        'OBadyyiygkXU1YKpngkVrE9PjE/Nnu63pDamLjD6iq1z0hPiMpYEW7fH7FgWddm2P4deH5yRyQZ2z97SEnYgaFH+btcVWyTv387v'
        'QY+NxFCQolVUzME+Hc6ihD6TAmElNo6j25rEVlMzOXBovut1PYXEJYwKcdh/Ex4aLc6w9fXqslmRjlDDaBVV5kyLZFmX33TT5Yd7'
        'l9fv+OWqPYenFRRMeyaywJT41HX7n05qX2MpeWiW+TbX/aX+a3hP3MoZs9fERQX071Er2i+BoVK1RRULQiC30QY4EgfLpNgJjPGi'
        'BX6zIqyxmDmI7drgq2RoGbAhNGs2W4ytIRW+3divFQ+CppNxRzBRmYO6gfgY4lVEkiOx/KTE1lbh35yLK2fkJKXmTL8W/77rarw8'
        'd7hwuLRqYyHImZOVhR+5lyttsZXikUAChoYEk6XWgmADJh7EcLKWOCmI63KwX7esIVJFemKMiFQhHMid4gMTbqSFPqXSzi9UkrZ6'
        '/Hv6AP4tqX189T0d9zN79FB0QcxQzDULpg9NL8DnFb+F8+3pK/cuVMg8DWRiRcNGY3Vb7OeBPzWjUHVwufH0Ql8yiAVgw1WMtSE2'
        'RljB9E3VITZlBJMCIzzU4aZOmik0bfU8/Dvy/HfU5VvXrD7wgGuYXffAgdXXfItd5xoWka1Gzvh2AJEF2kVsidwtGFbMgnwcaK9E'
        'BA6uY9zPpz5eCtrRb/zxRjwMGPVQON0ISDOgEwebfIP7Qxmi5/oFof2Dg8ktCRUSx0r4NFvF5rO4RcIbgK8LCUTkbnVCpyivZsr5'
        'NUN2KXk9sCoaJwEDoW5dC5GWChkn4InVDgJnAzhus9kXaQqkba18YBPiPLV+oaYtXbLwovqLQLr5NVVlzsKClOQ00TIpoanhYSQF'
        'EbhWqquhKRCB7hC2JC3cxyCMOdzBc7YDuYukMV3H5S+urYu/fF3D08x3x3W+JUfb2lBgdkheZ1G63T7dP8RvzaLdW0qGEpPachem'
        '5GVUzE/YsW3ucGpx07m/lZTNmpUW3Lbye1VV2CrR13PTTbsfyk4MDIiIsgYHBQfBmTWutnLJ4qiwPRFxiUFBAf6huTPzai8KDrWz'
        'y6aVzsz8voob9GWy4KZrCypqPfF8EczETzjHay0w22J6HYDphM1G0Z6jxXABvk1MSEtJSE9MhyE3GhIJNAoVGwMThTe65F6iEMaF'
        'SBokiGruiudn4x8raRhOrUYgjvjZ9l0X7X2UxTjnzC7tZFV9ZX3tjqK+KGt0X9nMV9nmPBihv68szvuBbxT0+tkV5QEIv+ErEYZ0'
        't4ijXcT4bdXx9POL8WuIiU5KiE6OSQZ66Smje5hoRTLWyB7mRg9W79JSVrL7+usvuaq9/VEWXjZrdmlr5Z5pB9ns4W2DO6ftqWR7'
        '0hz56Q8qYflr6vnmx2NsYjkX5iBRQqawDImwYdFEAAvsIldUhrz6qjXdvpf9YG2Eb1VVUPuKa597e2fBFbHRV14ZnnhF1QrbOwb5'
        'G6eVV5TaMP4F0tFEqKxZSV019CUTk/s1y7qK/fBC3ob4e6TtOJKWpKxBxkLCHjx4XY0uX53XHTyoBNrrRGzgYBXbez3CrHW0MJM8'
        '4SXJRHiIDEVnE8WldUsyFr9nz54lrz57zwPfe3Px5Zdf/uiigfxtbJPrDAt23bctf2CRWkr1BwmSQdVQi6Cqw2t9TuzNcbpV6mhU'
        'qnN62fqH+7c9vK5seqfriVsuXr3q4ltcxw5mD9d13L5ixe0ddcPZB69Zvn91d/fq/cuvIXa6jr2FGICRUHn8jiVH+YsYbZrovLqD'
        'V3SUWuUwj/uUrXRmpxfH1OWlL4kry5xWEF2bl9oYP84ztgGDU1DZ/oLgoKBAXE56/6TqfsTeYU8Cl9lk/y0KE64U4RaxO4DspXyV'
        '5zxX6R3CTcJTB3szsEIjJh/CNpw+Pp7rSvKyHNG1+RmL44rzc4pxl77kI0iJoLLbC8Rlxu3TvdyLzI/DX7TwPG5EwqtmPruMR5FV'
        'PV6bhdEB/l7GmNgtHsvuWgoY2ejZ0uA2t/uNdjuBXmz0ifhWZmZCAj5Hha3nFvWDfSUzPiErKyE+M/HA1/Rb5Tm3hNb9zY9zUQey'
        'tN/hDmEkWv029g73JcvF1Cyt9BfLXnEViQ/33b/6OqJWAvsn7/Wy4jh9I31jP/uM/d5lPzkw8OT7l3wgpRYSPkLbu/2O+VvIrhQu'
        'ExPkd98VGegzc8uWe06tOhV7NVH3dv5bHoRQhGJTuPXJjJTYSNilPc0S7VmrFEvSZe7JhV132QUDXNLaurJ0eWp118qWlpVd1TWd'
        'hXmhoXn2xLS0RLYMX/bc0NBc++3dy5Z1ZWc1di1b3tXYeIndnpycmiDSJKQmJ9ulGX8l+wlU8ihU1yoIq8JVITiiLmAihatpXlZK'
        'cmbajhYhXBbuaHk49EBQVhb7c1sPZMtiV2xrz2jSSUtZRiSm+bHs9yCe3yXvPwnijUc5adKjtL7UJr9/911Fud2rTt2zZcvdsVcT'
        '/D3sGzAe+mpzFx0NkDH1xcIpOaE2KUMQ0xZ7RWc1PG8+FipjmWWQ/Gb+H7Pr7373wN8J9IewS27z8JfHCrlNFv0ltpP9mfpQAIkt'
        '7FjDggBZAl9c1LaooX3R4raGhrbXcI+bxe0NDdImOA9c2YmInebHw/xEPoMnlO4F1b/qxrTH3sv6UtbGW9Oe+Wval267bvX+1law'
        'Y7PadnQZOD8JvpR+xzKSI4U0I5sG3HaIW6TnapnavEWbh8p0TiG+eebiMnPIyt21BbXhbM78xUX2WQv23hBi//6+iyqtptzM6VUB'
        'Prk5wcXN5XHxC7tLk2IDIqrmxhwKu+2aipqbH9w3Ky/Ylp4zozDKPzWTohqcMbVT+MlwCHGxn+ArUgfMDWC+mDz4+dJSvZ+/2Q8u'
        '/T7aWrFSnQw/MREsBhNyFSzGMU5qCh8hssiAeiJijMhmwSTWYrGLOV1mYaEd8UP1nQB27L7LzoxIjkiKi4HHWQjZfIJI7njbfIS0'
        'MPr9a5Nst7pnRVHRiuLipqKipmK2SsSQWYQTKZNzcpLZw4ZXSfrDte5HxSuK2KZztewnOcn2adPsyTmuacZ3PfpjSChhBvrUQMV5'
        '2iIs5jwiKVkUzHyFvQe0wal2NmYNMFuNtAwPDDMFBJjWhvqHwH1V0rN83DzjUFRmtojMJkXV0oaGigqdsg2rGlYuW1qxqKK+rqZw'
        'XuHcGaXjUjniC1DZPup3uiGt/cJbgG00/HBdryc5esENM24juRtLdOLLIBz+gM6fUpFkEkdni2NdxaqLjFDm2yA9HcmFyHMCBrzH'
        'ew7g/4dX9/df3a/k3mVYkhTjam5FtgESdHYz921RJ1mL6Cu696RYNg03wBSjqILbQ+IplqBnXE177kz822Aqi0eIYXcVPvn8qkdd'
        'v3+Uv/R5uan485eVFnjGVAkjm/lxi69IijKihWPyl3vfXvnho67njrDaL53jg58fp9G3G6Pvd0n6WcWYGB1uggRNCTcJKfnRR9zp'
        '+vYvfsEuOvffWayclfcfdH3g+uCg3I3IzvC9shiRMRxhOfEJTfvZutUffNC8vpfd1buQ2VyfLOx3+RFeOfzvEOoig58ZGTLKEHcy'
        'qwwbWQ/3uqzss35KfeW63vWrP3h/VAl+crgWp0OURZtiVyNR8wePLexlf3f59S90fTIaPhMIZUQLksKdg9kW9iOypRX4RHywen3v'
        'Otr9rTXyYCzyi3HBROkh8WPPnj3L6vGl5i4z+CsQjP40lmGTIRLhwAZTWngWNgSc6jh1avNdXV1d2HLf5brNdTvr/OY3HybIt7NL'
        '2FnjiBOKEafVdQ8767pHNdFFXBwxYH6ckcrDUpiTJZx7kWee+zUlYDiVqpwSSAiMxYp3vNz1tuvtUSBUGUgxw/X2eBCodiwUEFii'
        'KEVVTub3ReVoDxOhkZFlkZiwKzvaBaze55+n5Do4kVycxyto4c+zIgktVvRDiRlLaD8xBrqvSSZPYeFp0YRkxwmCzZ784VjYYgmI'
        '0MVwDuAoXyLNrmjvUD3tpHJj8WACAmegQ8SyZ1x1bPn7wkVzLY849wGxUb/2kilvUr8k2ABjH33UlPd5DQ3LeoapqZvIHCkBCBCu'
        '3ttdfQTlO6atwLMEA8Aj0koTlYSV8xlYkQuFeChCCL9i7KT0FS4B8oX/qBfNMlsmMPHzMWE/nb9YUsUOUDGwWsUuzI10OqgYAXxp'
        'FwcS+pto450P84cSP3FqrIY7nZrmnOecO6tc7KjJSMdhThmZNks8bYs1BO2X+2XcG4ajLWaPld1jVUYw7DJlVGUVz3UPvHz1pd/Z'
        'dPGG1NmBMQ25TRfDzJ6/yR7IwsNT7Fd8ac0NS7+yrwPaVFwq9wtOzCmZ1dD09cFLf7h12V29229IjotPWrOmtndeVNg78fGrG4Z7'
        'F+zftPuS2MEElp6etMdS7Vwqg9OaAkBgoWo7tUvhbQGjuM/0griIcIiURBwWq9sm0g3jpNgZLeLEYz1JRAvQf3C55c6YrFnTExnj'
        '+ebDjyXfmV+SlYGCkyNic2U8X3dQW/dkF8qbQ1zokD3D0BkdVpZlVmGV5tVkZpa0VldsdBTPujT8UFTidW+UZG5rLEiwx8fbY5Ia'
        'ETs6rTQ7uGt95brczIUFjsb8gsbi8sXZ2zOWL+1wfLkwJYn9IT02MTk5MTIt3nU0c294nj1DHuy2m/8BgeCDtGzsulMHQIqD2bfR'
        'gVhCcRZczIiL0+2+8NhlyjYuxhX8sczknqsO7WTPPNr8KIvcvX3XpZ9fwf9yLlQRnpOCIyKftdPktzkLc8XibBxv5gCnkYVUd/bx'
        'Nfv4Sg40mS3j+fpINx8RMqxoem6Ol5NPAFQRMUn2mZKjj9sMpubQ2Ufa249s3nykre3I5vqhqqqh+kX4Hq5vH97e1j7TsaRwZnnh'
        '4pmVbcHrvnHxlm+sW/eNLRd/Y92W2UMXLR2aM2do6UVDs/P6Ojr60rdmwn/Zmb01S/pBuSufj37zkKj+sSxm9hOOAGLmUiL2AmKL'
        'SpeBBv7YF9gmAnmZff3MsL8TDQKIBlaiQXyFU2WTO+Gmmg+roNMLBPkcRQUl00vy83Jh4Uq1G0gYODUSmpR5H/wqYoTAtI9FtQkp'
        'eO+zC5oy02YPleTufszhmDExAdnL9bUFlSGXbtnySl7uqlH0m6YVaYEV1oLcHHtUiFnzKcydGpJpU8DwOmDYtKB6CujV1e/5o8CN'
        'AjnBUvgSZmNztZKKojgsnJXmxIfCxqjO4NXkCVIb3SYe3qA2wk3P8LV4Yvu4zbNlbqGpsyYtKstIMGFq5Vlaf6Kif3TVNFhs18cU'
        'zmhZHRVVvXNJRXuBsNmWLYLJNiLi+gO7pjnjigJ8pjnSc2wPx0bdm5AwMyohJjqnsz43JTV/9oaSiKg7C5IT4zOSEmc0lGdkZOS1'
        'bGW7ghLsUdY4hIOJS40Mjgyg/RtD/PfQ+SxYqIDbrJ+cpNPEGV4djmjyMoeDVGTajg2saMPwn7ua13R1Lsic38lXdnS8xeYfOeJ6'
        'eh/+EawnWTl/g5aTZpAoyJ8kQsY4RxfI+KkTz9muqsrK0v9HJiZGRiQmRrAnswxPNyRFiIcRSWpK/TH/PvxI7KhaQqxZHuLgAY/l'
        'GxlJJBrlhNPxDZZIlvNIa/s3Wjc92H7ueNIVC9qvnhk8Z//FP7Fvm/+lxuCN97dv+/qKVXe1hr+XWTJnaepFc9iBk2nTGn5B0c7O'
        'sB/zj2AdTEdx6ckBcgaP0yKwnlfmjrqifNEcstFpXfdbHUHO4tC2pnVrXw6LjAq7YU0nYmtHBrc2bDWH3mwLuHdp65ZlX1t2KCku'
        'yb68m52tdcZFd5Of+6W8EDqpWUshYkf5MOUeow0IE3u3CulOUX4d4cLt4ncHfvRQW/tD/BXXtx57jMaGZzgjjX/cKU+0ccrjmZ6E'
        'ph27665H77zzUXblwQceOOhSrm3sX4AUrhVW5I9nipCL+v7+Mf4Nhl1jVi+Dmcda9uht+Ce/Dtxy6cH9+w9eessBtWnoa5NvGtq3'
        'T20aws6k1VPdmbRv3xOU72c/U33iPf5j+Dg40JJ5WWGiJcMmPyo7Sh2V7dVl9q2IiW+w401KxOyii+anNYSHVyVOj8vxm1vQuOgp'
        'd09iQ8FBK0MiLTDk+5tD83JLHMG2FYFh4VbswQuZnlvgNPYyeGDM1H7If0GbIYup4bOkx88qctVei+gKIsJO4zjbNgUn8Al2QB4q'
        'wEHs+Xn2n9I1P5nPhM8t7u15+hWW/cdQdgOVnUklT7r7dHRpdlWCB7LGXCZeNsL4u1PZOcUc0Wku09O1X+fvgnddLci5cao5LWmu'
        'bzy9lnJy1zkcSHYaB80IzsigvJN55wsAJuXu/tzDa29hld9ccwv/GAo+CBLJK7T3+Kfog9kEKNHdB3VUiCyLDV0RcRhEV2y8+65H'
        'Zs/+Nv/0WFOTF6AcApREh4XWe53dJ1Y7FyOIlwGS8F9//9uzZz9y193806amY4C0kJdqT8JHx6ZdJKNwi+DtMcopzHMG6jo6hXTp'
        'OKejqjfyJB0s8oelhOkGCjSnI0IXX6s27S2Jjd+7aRUvXb90rj1pKdwdRi7BrPuQKfrfGwP4JGNAUmVmJv5Xif+IdBARHh8fzrEB'
        'F08zMvCiImN9fHhEXHx4eDyYRONVI7fyDzyGGUEFeKXCLwzmrwUI1Dyfdo2RhxXXTG2ecEnCc1Zvf+ZlkElVZhqXllYXlZeWlBc1'
        'b1rq/FisrGVFzs3lP5xmC7QFFl+RExhos2G780gzn6s9xr89FU4VKy0PsmbXg/zbUM9dmbx0ZLYpGWOzoqU47R0CFU7DpIOMOXNe'
        'OolFZaS5WZcVlxoP1JEeYa76rJxZgWn+UTVJiy+annMHvzQsKsXss8LiX16UUWbFLBzOLkzbwd/HekedZCO5Eq9i6oApRXl8neDJ'
        'pWIlXgbH8X6OY9LCPdyqojCY0zrzMw709/LdGdNS85u6hFgZmaE1jLw2dbFiHiVWhJB6Md9uzxcfcGEVAH6PAH4hGWmeQEbeVFCQ'
        'LMr4gSjHWKS7aOb6revzkdMjr0ylsYVH0ivYkVqEbagjl434aTfQ0VVVlK8syB18UKqb6C/YniL2lW8j9+ImpXlyog5OvMIJOXo/'
        'NetHVaHbyOMngX3JvJC4tJi4fGfqnWF5+SvrP/MzNwWFhYRHNhdY8nOd2Mc6csNItrYT0EK1NYSE1RNaTDJAtDqEzh1abB0d37Z0'
        '7Llu6oU81y1UC8mI9FHVJuqK6Bzu2VnOwsyU+3IywyAIcme/WViUOSciKjsqOMy2KVgItJFE7cmRl/5XBJp5XIH2R12eoe+OrNAe'
        'G/nRlJpT77uztnltYTpvxlG7li4sY4/c1oU32/hc9ubUxIwwe21jna7bScyMiDPMd9KAeH4BhSJzv177NAZAZPwm+0xbbarGlrtC'
        'ypgx1hvaY+sO1AIjQiN0ykubcaQU6pGWDRsuSk5OsrPPVixbtnx7dExs1A4v+NMIfvJYibdWSLxGAPYM1pLvnbLPrrInJSdfBPC8'
        'D/FcorcvX7ZsBSBfgirvmnqVK4TyQFU+PqJp80ZenFr/jkyrvOKKGS+KbHyWNk949k6lPMpmMkluKGPRU9NyBDdsUEqOyFjKvvy/'
        'pAaEGXvNrrFqgCi9gn10gepMuFRnYr3UGUxR/Ni0/5RcjBpPLnadVy4aqjNlNS9cqnnHjGqe2Hg5E7FpvrDyHjbBwDR/Csq7KFt7'
        '/EKU97BxSjAq7xfGnPCfUrq7IMM8qGAXooHrG043jNLAAWoutuNOWerFupUrcFY2WOh/ebCLGjPYtU4y2AnKaKzk39WfJ1tDueJC'
        '9GegU8WO/vv6c/i4+nPslNRn1518uTbNFAgvkiVSkoWNapsmwzmyXm3TNOaAWZwjlRYmDpgVWGkqKhh80Vx33h0Q+GvXG3x5S7Mz'
        '0NqrsXOP8OWud6nY2dL2EiaLFCfZypPzhKEglEozPjMWBCbwFJJ27pEbA4K++rqnjJE0vnzkpMk6KfNaPaPCqaNHTVaEyR4pNi0Y'
        'edX0q8nsWCL9y/fea/oV4oy4rgMJuSkRYtwzjgoDlsEnTRmywlJSRYxYmjmo2BjC8TDF9bJfQGHXwh+7fspvsfpvn5fQB7DPmhZo'
        'AaZzGJ5TJwEZDpDgA+YJtSHgnbUE5LVmJj3k+th0mdWvF04HHSD6ERD9YyAaKLbMu2Hph0Mi3ve4wM595G8t7MpKvcXlIuzSEgR6'
        '586Cuq+ZSnCG62OScXD48zGKOVwfL64IGtIso6SkIaSpj6+5C+0owvdxCveHvdurKOifHzbZ+ohjmOPJgISkeNc/aVqyv8FLDUd3'
        'qOQyMOC4qeG/bItA4FTxP83fmqiY0+0lhjq6505pTmMYVbFanHbu7Oyi5PSA2JJmi81/zazidVFBAbVWW0KgtZPvnDlzQWR4xoZ0'
        'W1Br//Ty5cnBIeEITJwfmgnPa9cNpvlatU+INo3FUbjKscQJoIP0ENlQ413Y2eBr3gyUfX06ROVFeBVx1cg7EFEo1emgOSK9L8eO'
        '3ylkSNAL8Mrgs22i9EljCvDpnSQDIpdSO3SNl4XRnqFVjHkyUGxGWwRi2Kbhf5rwxNWM7nreLZGpN4VqCdcNM4oSU63RhTkZfjbL'
        '8rKCFf42q60iIsbqt9HUXVRaER6Wmp2TGRDU3JOTWxUO99Gw0ISCwCRENzjXAWZ1gFlztTuJKuMzatJYRhVVoY1N0RT3MoECAY/l'
        'Ua9kZEeegD2NCRVnXhgxlE9v2rmOWYXEl3nZvja/tTOLm/1sQdY6f1uQf2SXzpl508GaG8Gai0ODgoPBm8GR0alJ4M0zfBl6fzgU'
        'kgISWWkYVHx5k9Gbhoutvdx3sVqjxvZUEpQGN5rfOBzfxH9+eXdeXrdYwNQgsbhpROhAU4CIVW8jtFeKiu7Df9POVYWFqwqB4+No'
        'sxGTr2eNJEx6K2LU6RwtlclbkYnj5UeFrjgWlpIijpKXIpdiEIGMrse73j4Ydzd/eO3WWLFO+jok/qemd1DUJXKz3ETFLDoaRSHL'
        'xytLncd4oRg2SxzF6bAe/F7f9P2hmFtMN6/qisKu9XO/hOD+F5FirnJw+CJk8Cri3C+7vtcb6yGBP28cud+0AgaWGuKI8lix9b1e'
        'BKOCCkJh3LC/swWmbZgvVgkLN3o1/K24r1BscfpUSkoYjmfwU3wi46OlRKoI32IyQyWTh4Nr2cKL6pjPZ0WRYZGRzdPnzU5z+lnL'
        '03ljZVnd/Oas8IiYiOwN0aQjnbsWePkQXquOSZTkqcHxOka0yU1gAhcDgVa0cNCIMeArsdwo0gnHgmAvdMGEElXH+KieexWo/ulX'
        'CtM0+8SYul4Evz5m2gV72CVS3bChEcIDhZtNYgR0uiQRTU7tYbfLsHNd7hm9J7qAr0jWKJwk3JHpJkjTXBGId3COwGmHOWalV3BD'
        'JGfpeRxh2IMP/fDsnNzMwLJpebERsXFJ8eGREdn26PhZfHlRTna+T0hsWlZwVSg2HFb4BYcmhlaFoQk+ESM9/8FU9Cixb/PcJ+y3'
        'rlT+A6Hm9YFx36Os41mUKHUfu8R1jUxNBZmmQXaqHm8btSoqyuRrxNR2ideqqOG59E/We3yK00EIzbtXYNT9ho4SFVIiR+BQVQDg'
        'EHacYuAQbM8jt9szcxDIvvduFlgDIie0/2yaQdPOdol4pmhjtJIIUNylIkpgWcVHoSpn5/EiVg0l4f0TpUEb22xiropQ3SF6G7OU'
        'TH3mmGL0/0RFA3mFo6Sizunax26Mjg4JjY4J4T8orq0qLK5siA4JiYkODcHBEYIIIxaF8jKJbvwYdI0ESRiLqYE4XkgKBdIxAYJ9'
        '3/GpLCmZV+t0vcWcMTEhIcCR/6CoTuEn0AV+Hk7w12clghNixcQVLYVZLPyHaDIrYkZrQiOMoUntwNhXzU/SaONrjVXGKjHeSK54'
        'bNfMXcQW3V6M4a/NlIwRrsoTIKVtUwzuYbIk40O9DOHc44Hfd+PG/E3EJAI+d33K63CQcA2079gpTD6DEHI8KDYoJiIMGWwZ4nwL'
        'd/d2O4wZp54/qE+dlYr/9c7gKBwnEhkVzOsWOtPEszTnwlXRweKEkeBozSQR8YlEM4Zif+jMijKP4537mCWTyXeV2yPL19QYFubj'
        'E5YYlhAT5RPqE5IJn1p0MTELCpsQIcyPAsfg5BN5s+uH46P1LK/TAnzKNRluAMeZeGY7+oYZGc8I0Zl8fS2rRDQnX3g2+Vp8GxMS'
        'goJErIFUe1B8UFymmMhY0eLeE5mJUTXMl2rGoGx6Ws2gJkL8CSC+xacBXjYzwGDXTaDsW+mc3VHKvr+vz2bjVMdfC7D5B7QFIUCs'
        '1bYKF5t1LU4ftFmFdm6Tx5uO0uYvCITQX2ePB8K/d8owxCRhzliN/0KAIPrRRBMHAmOYzk0MhWYTCeXlubnlNeXV8+bkzsgtKy50'
        'zy5E1KILmF1MwhxPTDzv2DaWWx6YZCbien7iHvkvn1kiEC/CF2G76Xhu7bTBQ3icWiz+cE0Tezrg6udvaYyLs9niEEvXnmSLtcVk'
        'SvVanOpgVK8nrt8bUvGOGluV75AqPj7bs5HskWkjb4y8OYUVT+tYw98DDkd6eklJ+i9xEbfCkpvjegQA150/8rbR7+F+h4TgesQD'
        'yfV317sjJ0d+iQxKkbCOt9FprVhdahy70Uk+h3k1JVVXJCweQZL2UlB48lB54d3PhAf3lpRfQcVdheJWori5cpL+hYqCcmEyFPOj'
        '4LD0oZnTb3P9OCyk11GOYdm1wfXHkddRrRh9dZsGKE4i0keteqzzFaseS0EtnOoUhrCsutKgjY7HWqw6g+v9Vf62lMvtMaEh9iuW'
        '1rv+OMcRGmhdm5BUig3R/XsckMOuda4h1HAjtIWFcpYTgZ4rCtpk0uMEp2sYHOMmxkhqqzggLCwdSEFJGIWQB593V/vb7Hvs0SnJ'
        'Vy5d6Bqa7bASOlgW79pB2ERjpP4JLexNuEDHwPSuaLWid+5NZHjHFIEGqpXxMSJEt+K+6330BXEWS+hPPGkVAa7c81Zm6FiuQKfz'
        'gdLSB/geOQ3m5z7mda6P1EBfeEGDvB5Yenw5NHOqI7zE4N8e4UnbnUxyuHLvvTf4Aob4c89DzoX+B4d4ywUM8cw9xJdf8BB/7ntA'
        'fNt5h/iAf3uID/z/Q/yFDPGW/9AQf+57Ew/xm/8jQzx1Sdd/eIgX8ZSmNMS78uUYH3hhY7zJdQ+smummFjqGIR77rCNC/DA/xT5r'
        'YbafyJHnoZvqLl0zymZqatnz0Bir6STwhTviRPBdv76p+NImABVgfponr+MVMDIykmYqhQ3oQ83Cfw4Z+MeREdd1plLh9Y8nr8kn'
        '584izWs+0XjyukpzxoQdO6a/48mb6snjSDOCFUIL/7V8AsiXjZz0KZGQ2TSCfBkgz5eQxRNAvgyQN0jIlOaM6VJMTedIyPTkcaQZ'
        '8ZkuIdOTjZj8BmN4A+SR2ZoGOLfRk0QBeSSQnsygJ6L010fmiCdwxluGJ+EC8kgwpXme0vgKyCMikBP9C9S+JubvPv6476Wg+uIe'
        'IYHwS95zbOy7Qt2btGLtWnXvg2WzZ9S9L8Jv/FLdm3H/sbr306KYVd37a3HMru6hI+I0b3lv0+xsk7oPTLUxvawgrSTtgFat9Wn9'
        '2i7YGLu1Tq1LG8ICVzYGiBxci3GoUxF2wuThvhr9pl0bROpe/KrROrSteLKFUnfj2Wa8qUA+T6p2d5oCPO/DfY62FOWIu34qZwWi'
        '21Thdw/SFiFVIZU3C9qF2Fi8BHdj0+e7c4x9Z3e/W4myB4BHt8LXA92YyxuesYae+i3C9xB9Bui9KKkDd1u1HfRXcJ4666m2jIKj'
        'v/+/S38r/laglG6ksWt1lE6UuBx3m3G3A+kHkM+uUvTg2obfvfjVQbUfVpAHcD8ESB2Ue6HWgGsjatJB+HkgN3hBEDUZr23Ex4iZ'
        'd7k6Nm1Eq26FSSuuPXiyg6C2EF56yha8EVQQd9vx6cbvFuToIWg78FvgLt4KXCu1i+h+SJsJLEQbDKGcmdjiPh1Q2qhtBL8MAstB'
        'glUA2ANor+mocx3qaKW//P8nf1YD/Zdqteg3ok6NuK4g+i8E74iny/E9EfXtgCP4rZTydoBSA2hpwQu7FB8WIjT2/7saWlGzZcC/'
        'UluM/tqAO8ktojU7URPZ3nbiYg9fnp8fRe+RLZhDHCB5f4g4ZxDXbvSaYeKdIcU5ot2FtBA8JPqBlb63K17sR/oOVZLEpY2ki+S+'
        'Pur7Aup2grbZjVU/SaWL8bSN+CzPgMUw3vZT3iFD3Tx52whrCVc8s+LXZno/QLB0TFqUdBBSQdDA02d6SIJ0oqRuVes2hflWqn8v'
        '9RfR7wa9+prEUOK+XdFD9qnNhFOHO62VaCPbYjNRQdBJUnML9dpeom4Xld1lqJ/AX0ixXarHC4p0qZZq9+r3W92YdKgnvYRdC9Gh'
        'V/F9F/Vlq0EG9CmaDlD/tho4S3KGlCZS0gwaWmCsbDTiLGkjMR5WKfIUVw3jvtv9ZCtSit+b3ZJNp5mso2wTIYNakXPIXZakcA9R'
        'pkVJzT5qR/23xHSXgbN7qbZ2ko09SorucqfcSnj2EAUFLeyKElZDzfIUZduQTtZDL7GXIMmxoZukrofT9ZaW+dsotU6dVjWm9Lgp'
        'IjBppV/t7meTU0NSbDqVYqydUdJL/AbHjHTe/NuuqNFCdNJzDRBFRM0kd1nxXPLw4DjUHXZzROuUaOKhtDcP6bw9Xn5BSTFWCa6U'
        '8mfAQFsdE0nhAWrVDuKKsaO4XkdPPxAU2EX9VZcd3rxu5AwBextJjgFqN136bVZtMbZPDCi9RPbP0frE+ON/O3JKWus1ayGpKLjf'
        'quB6OLAPeYcNuHgkpF77QTffDo1D9z6DdtNN9+O3gJQWNRiN6jDKLsFnBT6NNNZaEbB0Yv0qVdFhs5I7Om10bEStPWPIZtI5ZP3H'
        'tqWxB9vH0Set0HJlfxBlZSNfzpTprnNgmypzQMmbrXS/xd37BtVIJWS3zh3dBtlt9ZIZHaofDgNGm6K+XsM8JRG6VQ/21r+MfcK7'
        'lT3jn2yVVOgL3n3WqAUsUb13onbQecnYywepR7SNktTGmovfm4nLPPxjVVqrt4Y/qDD29BjZLjrujSp1N2HQM0ZvOx//6FqH1Cd0'
        'XU9y02Raf5uaG/XReOmRQ4Ok54wve8/Hf/Zx+E+v5+IxY9/U6jn5aLNV6Tk6bi00knh6fB9xWbvqSUPqTR5pKQOqPVuVJjRENdXz'
        '5pOe7K1Z6PLCo8P0qXmGTO2Rr5tHtdBYShvTWM/LBXnuGrbRiNWr0na65e9WootHpsnUujY5WgZOxhk63a2E7w4apXtp1BygXDof'
        '6y1bSXTropKm0oqDVNNe9zjW4a5Nh/uZHKk7lf641f18iPi8i/TUNqKU0O8GqPVkX+xT354Rrl/h0mdoNdkqvePwuHfvmphOBWqu'
        'UgvpsxhjwXKamzXSnCyTeoe4rxk1UiwlXLZS//LMzKT8lPh2qJaTde9VeOV5adr6fENqx51qtu1Nae9a9wHqkBqJJS9YSXvXJdZo'
        'np243p6Sht3zfF3T3aX0EglTarwdBgw92p63NryLeuREWp9xHiK11p5JdGk53o1961lRGJywttZxaytlhD5jG80hm5X87SMNVPay'
        'NrUq0+2WyIO03mDF/DuHxqQOpa16r65M1it7FWd7y5hu1ee7VXlStx1WMmQ8yZOnRmj7ODJHlnA+ST2oWs97puY9y5B4ibbarHpK'
        'MdX8i5c5dQ4djdvoWcf/1vwi7zwzjA6al3cZeojVLYVkzzTOOeUqwnb3CDJ6pJXacbfSqjzz9PH1O48eP6ggeuZlozW2dsLVyJ+6'
        '7jOkysmntpNcJWXyTjUTMOp2XaSziRz5SitvN6zMdakn+jgh6K1zpocG/Yqi/VR3fW1mq6KkHDPGg76VRnv5bEitU3QTP7ZTaXpr'
        '6uXpNZBYtCr+lGtiRp184tl3n6Ksdzne81+py3crzXo7pdwxrm41rPRZ2XccSmr0TaGnfJF+Mqxw1/NMrE9b3fq0cXYhqTNINdxJ'
        'c7Vu0p6HiNJydB5Sa0L9k4yA3mPeaJq0UevI+Xm/W8LKsex8uqj3TEXCkH3fW2vuda+y9Kt6dIyjc0tu3GrgEJ3G+ixC16T73esJ'
        'vRNoGHpL63PMEqKqvkbQO4ra3m07NQ3ce5Zr99LXxoc78Xior8nJMdh77cGzFmJcLdxKaTrcml47lTuo9JgBpbPLVY0hap8Ot4y1'
        'npfb8xTPCUnXbxidhXzYQvjtUHK/04vDx2p/Et549LBOmc5GKTwxpQe8RhPj2sP5eo913N4j+cbpxTeT629jtSOJ1XiaU96UZ0Fi'
        'ZN1KXODhiYlGWdkfutUax64prlIYNUFPSUYunHjuer51sInGS/sFr3tZ/+PrXvYLXPeyjrvudb65zAr3XGYJOFeftUxmq2slnbjP'
        'vW7SSxaUHkMrbcfbbrVGv3nCGfJoXWe07qyvu1rdtJHju74qJ2Zf1Vi/r8TdYqqFlSy+tV72seW0yr8C9uZKsjDZKZ+d7E2NkCsL'
        'aX2vBk/EnHa5ep9KXLeK5nELkK6JYEkYy/AtYDcrC4Kdfotfi4iKNdQnarXVyqa1nKA24t5OmC4lm10tpbNTDlGLJqrREhwALKzc'
        'srwlyKXb+BYTLhLTFXjuKdUbq4VUosTMquhSjTrIt5WAvZDgCfzziFLifokbzzqFaSXRSEBeQRbGJqL0MnrahOtSpJMWx0qqs8R2'
        'CdWhDu9lXWoJA1GyVdGqmqyYzZRiPvBaQVgsJd6TKfOohqI+NZRflLqInkrMGlUrLyOdRYdSoGgp8bDj/UoFT/CAqH8D2XpkXus4'
        'eNippRuo1GXUCrWK9pXKJmmkjqS9h//yyGpfSfjOd7fBaHx1aMY2sI7LA3oJ86kWtUSPBiplOa0/VBOkBjcPiZzL6PkKA19J7pYt'
        '32CgYbVam6iFZbxJpZDwrKNqIfuBwN9TC0nnSvVd7ZYadkMbL1FtWO1u0UbipbFUWUU9rpZSVVJ7LFdUsBInNSrq6r1QlqH39CbF'
        'hY1uzLzpq/cWPd1UJISEpZdt9WrBGrJSNygMl7upcX64BV/I80ATrs/i38gxzKbH+WcSG/jFuWMmuAyfELsL4Qfni1DMFkRf/QmO'
        'zrGyAGZjgVorzq/6FgtmISxUa2Nh2iPaTSwcvnOZ2jltRGtnESwSTqTvsigWzWLgv5utdbA4Fq+9yBIQlDiJJcP76CWE+07V/hvH'
        'nKSzDJYJ7WOa9hnLYtksh01juVouy2P5rIBN1/JYofZTVsSKtZ9pL2v/Yg7tFVaCAN2lrEzLZzO0AlauTWcz2Sw2m81hc9k8VqG9'
        'pRWySq2IVbFqVsNqcR7YfLYAY0ax9nO2EHsnX2WLWAMO5V4C7/VOtlQ7yS5iy9hytoI1sZVsFVsNl+Wb2Rrt29pRzJ4+hFbtZGvZ'
        'OraebWAb4SNVCofdt7WzrJW1sXbWwTazTq2MdbFudjHbwnrYVnij/oL1sj7tda2L9bNtbIANsiHtl2yYbWc7cNjGLrYbAdIvReT9'
        'y9keeFqVazPZlewqtpddDW+m2dr77Brtu+xL7MvsWraP7dfmsOu0P7MD7HrwTTe7gd3IbmI3s6+wr7JbtC3sIDvEbmW3sdu1HnaH'
        'djG7k93F7mb3aL3sXox197H7yPLkgk9vHzvMvgZ+e499Hb7V97MHwG39OHfkQW2APcS+yR5mR9h/aYPsW+wRbRv7NjvKHmWPgTPr'
        'tX+yx9l32DH2BA78WcSeYk+zZ9h3wVdvaEPse+xZjL872HPaMDvOvs9+wH7IntcWsxfYj7Ql7MfsJ1oje5GdYC+x/2Y/ZT9jL2t/'
        '1JayV3DY28/Zq+w1dpL9gr3OfsnegAa7TNvF3mS/0i5hv2b/w37DTrHfapey32m72e/ZH9hb7I/sbfYn9md2mr2jHWbvapdpj6KH'
        'fIT+0cTeY++zD9iHCIH5F20l+1j7k/Y5O8P+yv7GPtH2sU+x6f3v7B/sM/ZP9i92ln2OkfVydg7h8q7QrmQjXOzQRfwGbQ/2hsMx'
        'llu4H84nt/IAbuOBPIgHQwqs4SE8lIfxcLjWr9M+4BHaMzySR/FoBNCO1dbzOIRYjOcJ2ve1H2h3a/fwRJ7Ek7ldu5On8FSehgMi'
        'M3gmz+LZPIdPw7HReTyfF/DpiGhaxIu5g5dwJy/lZYi6X85n8ll8Np/D5yJsTAWvxIGv1byG1/I6Pp8v4At5PV/EG/hiHF7QyJci'
        '2Pwyvpyv4E18JV/FV/Nmvoav5ev4er6Bb+SbeAuClEYgokkUXP1j4OsaB7/OBO172ic4jrBN+1T7O2/nHXwzTuru4t38YpzN2cO3'
        '8l7ex/v5Nj7AB/kQH+bb+Q6+k+/iu/kl/FIc3XI538Ov4Ffyq/hefjW/Bl6M87TntS/DuT1YOwLPxK/DCzEUWtDX4JloxTEvYVoV'
        '/xL/srZB24QQwxXwP7Txa/k+7XGECtzPr9NC+AF+vfZN7WHtOe249iPtO9ox7QntSe0FfgO/kd/Eb+Zf4V/lt/CD/JB2Nb9VexZO'
        'lLfx27Vv8Dv4nfwufje/h9+Lw1oPa9doh/jXtAe1Fv517Sl+P+RoinZQ+4p2F8Iu36Ldr/0FvpE3arfBM/LH8HD8qnaH9gDOLnqA'
        'f4M/yB/i39Se5g/zI/y/+Lf4Izh34ih/lD/GH9c2au9oafCgvFa7TtvPv6N9STug7eXH+BOQzVchQOmT/CmcqPgM/y7/Hn+WP8eP'
        '8+/zH/Af8uf5C/xH/Mf8J/xFfoK/xP+b/5T/jL/MX+E/56/y1/hJ/gscXPZL7Xrtf7Q/aL/V3kRUvN9gzPud9mvt99op7Vf8Df4m'
        '/xX/Nf8f/ht+Cmcs/Q4BjP/A3+J/5G/zP/E/89P8Hf4uAri+zz/gH/KP+F8QBfgM/yv/G/+Ef4pjIf7BP+P/5P/iZ/nn/Bx38RGT'
        'iH6OgGWIveRrMpssJj+Tv8lqCjDZTIGmIBxVGGIKNYWZws2VrQMd2zssw73dRbWVtfJaVaquheparK4l4lpYVF2j0peoa7W6qnyV'
        'M9S1Ul0VnMpiS+XWlraBvl5LZV9nX2/HFmvlQHdvZ0vb8FCHpbKWrgHVbd0DbcNbN/d07LRWt/cNtbS1dfQOmWvaWpARl4G+liEJ'
        'r1CVW1hrrqVqmGspkcJW1aZaYVWtsKhWtakusda6wassCvGqSkutQrRWIqqeV5vnUwkB8z1I2ua39W3d2iLhWOePAllc6LOgtWVA'
        '/agMWODJqJ6V8IX15oXuZgB56xSCinzVMywLFTYLJTbmhUPdPe0dAfUGLBYZsDA3ECnNDYSsrcHwyqcBCEq4DkUYh6q1Q5VXUmxe'
        'IvMvkfmXGPKrJKrlS0pNtb2d6n6GudFQi5oi+bhGkb1GlVKjyF+jQNTozaMas7rWt7Grb0A1Yo3CqVbPpVLVqMatLQxs7BoGCw0M'
        'b+1pGR6yNEpKBTQO9rQMdslqLFMXWZtlY2rjVIU4FXBnrXm55MXlBgIvH5OvVFWtVCFXXiurPqPOZwXa3LzCzY2FRTJNYXGRKqtU'
        'lVVaa24yUs2hrmXqWq6uVerqVPVW1Kst9W3yUKtW0bhOIVarU08VVlsb2ORFrSbFV02Sr3ybRHc0NxF3mVdJGqzy0MB/VXt3x0DH'
        'YPegeVXnQMv2joDm0ew8QzVMXYm5mZKon6qV62aY1xBY65pRHaW82NxilEWqE1SVqatipyqHujpVZ1HlVSrCVOqySeWrLFfXKnVV'
        'cColoYudRZYWRYQWJZNaPDKppUPSoM0gk9o8MqndIG4KVcGFdeYOKYw6jMJI79MKrWqFRrWqTrXT2jFaGCnMq6osHQrDDi9hVGPu'
        'lMKo08ClnUZh1DlaGBX5dHmEUVVA1xhh5DR3G7lRF5mKeNXlvPtiS7fCplsJo25iF0lOR1nAxQZsthiwsW3pHOjo6O1p6W3vbjP3'
        'yD7ZI/tkj1FC9XgklKKWQ5HCofAocZh7ZcP0tvT3DQ4N9PV3dZh7JazesdJK8UZJmanDLa3KzX3GmuryRZdaqsQa1T56v6vR20+1'
        'dnWdb59BWin8avVcKlWNav3aosA+r/7Xp6RVn0FaDaiLrM3AWGmlCnEq4M4686AkxqCB8oNjpZWqWqnO+eU+Q0JKDRmllHpXpMoo'
        'V9UtVWWV1pmHjVRTCoGU7bhWqmu1uqpeX6tLrTLfYYO0UjSuU4jV6tRThdXWBQ57UWtYMd6wklbDJK2GpbTaIWmwwyCtdril1Q4p'
        'rXaNkVaqYeqc5l1GaaWqXVdu3i2l1e7R0ooIVVxYRgAKHeWSEg4pbgodVZICtYVF8lpUKq/FhepaEqiuBYOgyJB6WqqelhqfFtaG'
        'tvdVd7W0twx1tXR7vakLHepb2jLUssXzJmxgeGNPy5YtXS29nbta+sSLsJ4xj1T+muBdfc0gImXv6RgcVM+L1dWhrpXqWqWuJerq'
        'VHjPULVUz4vU86IyddWpUK7Sq9+FikpFqpwivVxFrSIFt1jHQ/+t4Bbq8AtDhrr6VqB+oyuiF6gjqipSpF9VhYr1dAqBIh2xGnWt'
        'U9dalU7PVx3ag6YZ7hnTNMUqZ7HK4VCQHaoqJQojh2KIEv2qSFOiSFmip6f8xUWyKYqLnA51LfFHX+jo7uwa6rINdUHCyvvBgM3d'
        '2/V72yC6bK/6IRl3RqG6Fqlrsboqxp5Roq5OdS1V1zJ1naGu5aojSPwL5aiFa7G66h1FwStT8MoUvDIFr0zBK1Mt4VT0cCp6OBX9'
        'nIoeTkUfp6KjU7GMU7GEU7GKU+E3o0Zda1U56ndZrXVzd+fwQEc7BLB8VKRQLFJVqlRN6VRMU6KYwamYoETv23Uyn+LKwkpVBYd6'
        'XuUMbOvr6evdigYbahnY5dPe19vpUzs80KfeF/v0dA+0qB+ynQsrS839HYNIrx6r5qpS6EtyFxcVS3IWyx6Gq9PSMjDQt2O430rX'
        'AdH2/nTb3rejV971dGwmbi12Vpf6b+7u6elob+3baRka6G7pHO6XbzAXpN/tvSploXruUNcyda1R7wnBuhl1stJFRWX+HYNDUBmG'
        'OtrVE4d5a3evGOIGO9r6etVTJRgdqos7Csv8SSBjGGv1Jxks7tS7KnUtVtdqdS1V10p/GhMMOUoCu/r6trS09m03PC2qskGst3b0'
        '9O3wPCxWkrxYAVOyxqFknEN1aIdDMmaxkvTFVRKp4upydVW/peaHa616XqmuKl+1YlRHUZC6FvRS6yjmmhGorgWDW1t6etTTcvW0'
        'XD4N0n95Za1UiSq9ElV6J6pSiaq84Ferp9VeWau9s5apx2Xej3WJV6IqVOL12uFUj53ej0vV41Lvx6oMx6gyagLUVVDGcF9uuK80'
        '3Kuu6lAkcVQaa+tQNHZ40dihaOzwpvEMhUiQTjavnzXqZ5gBvbGPysc+qhz7SAcdqKsx1A3cv6h7uJEaaOke7Gh384HXz0rvn1Xe'
        'P6vVT5sOqguywqYDMvyoNP6oMv6oNv6YUSDkihuA4Uel8UeV8Uc1/dDIRsFGRrC+iOVsrCxqFKddROF9GRGbOda+/oqQGn/j/xQR'
        'XbDq6MPuRyCSB9g3sLz7IM5RQqh0rAgypP6n2N9MQYvrtEs1U01dwwqtEMN0r5YuhmqslvqQvQThM8kq4uP+LWLGe+4RR3VLxwA8'
        'KYzfW1sGtmjZW7dsFbvWNJVf2lekJQYhBkw7TUlY9d4J/M1cPMEhsbBBIFA/9nPbYE95COumD2HFUny+ph3C902G3/vp7dXa5Vg1'
        'HyBfSXHd5P5bQ/ZY/Y8h3t9+fD/Gxf1PxPfISXryPt9O99spTQ/d99B9Jt2L74v5ZXjySxFlbmQdfZ80ZVMaCWcJsNVwmI+GuAHy'
        'WmK4zpzgfvQz/VoxzrPx0lSMSj/+B3xAvKERVyBKrKZoTZZcBqsQ6I9WikOLB9EHNXJdhe/XXO/S/SPiHoeEICeFv68Zc0UMF+I8'
        'TbWyaMlS2Bc4WsUm4iZirXsm7EgFsIalYt09Cr8Z30HhX3axXeKb7uPofre4h+VH3A/QvUzTJvmG/UpYRdjv2FuaiEf/Ej4vqOtz'
        'husLE9yPfqZfXxrn2XhpPB9Newqfx8ZcZfoJPqDkAfEt6gLOWS64SNRu5CS+ueqZeh8RrRRDNLVELokq0Bqi/gtW2UJYC0WYkr8I'
        'yw77OywqsISASn8bOYH+/peR07g7zv6B62cjp9HvPwZs8Y7xTPFbGDvDC/32C7lhfkJAt/zW/B7sIjjIY+TwyKmRu0Y+wGk2Z/A5'
        'gehKx/E5rV3wP0A6ObILUM6MnMWvU4BGkHB3ZuTkBUO63PD7TUA6MfIC3V8YJFH6iYneXRCkXSNvAa9j+BM1O4m/I/R9GvZlbeRl'
        'Uc7IC7ieprenJoF0K9LuxfWMwlDQ6bQRJ/lmCjhdD2zWUruJ1jsBOLfiI/7OiI+njgIjPDs1EWTU7LiCdIZqcpyeHNfr58ZM0POk'
        'SIP7t8aFJOhzeOSs4AP8Okt4ncXfcXwMLUjPjkheIW45Ow6dTo7sVXwJDiKsBHeKmpzwptPkbUncs5dK/IBo9aaEoupzyt0WZxVm'
        'pyeBdFLSw0CN08bWnnLb7QKsvdTfiJ74vpU44QieHaanJxRfncaz04JqVPszqk+d1nspoBwnWh2nNKJ+t1J7HwMkyaPHUeM3Kddh'
        'N8WPyJYgaDqk6wkS/Saqn1KQBEec9OKC0+frd6JNDTx+cjR9pkonA/8KfI7rkFC743qb0PcJ2Qpujj87ugzqp4fddTgxWR89Lz5v'
        'XZgcmoxO/5l/I9cTd+rUPfXFa+fmzBOKN3SKHyGOPEm8eoIkneSJU3orjB43FCRdjrilouLtk/T3AjjTC1vJlYbfL1MkoNe09/Dj'
        'Q+0T2PL/Ba+cFPjdpMJPJZ0hgBt8aPK1BfCR2ao1wP/kfmiJHJqHjybOmEjCH4JTw8snHSNeBvwA5sKrJB0+HvWwka/GXzT8hjqh'
        'p/Rr+7QQWLgP4PsW7U5Y8u+B5ZzBUv49wHgWf1ZoEuIE++fxF4zR/afQc3+mvQoN5zXtA1j7P8RfHLwz/oayP9H+Cd3qXyxAC4cf'
        'kQ0HjuIwdC0CXj9ZWgxwrdSS4bGzFvrNOrZOS4OvzQYtCP42HVoiPGy2ambUZAdG/Z3sRi0S/i834UiWm9lBzQ/eL4c0Gzxg7sWZ'
        'q/ehtlGk78cCrzjCwEIYMGDwCbAUGHDCIAQYBGqhoFwMSo0F/UygH04JIJzCQMU86BP5oGU44ecL/NYAj7VMHPYCfyBgI7CMICz9'
        'CEt/wtJKWAYQlpGEpY2wjCIsAwnLII37PSS0D/9/+f0G2OYRn0qpLmXYkJKEJ4lnToHjjlC/7yN5dGTqfY6k4GklBU4RR52hv9Nq'
        'fD6h9xLJl/LNFODSSK349wRJx7fkn5RyajQ5DulEElzKwanoP3K8VHen5bf6O2PsDzSSnvbI1vNAPeE9SnvqOHb0vhCZQdrPYaKf'
        'qL2g4jH1d5x0h71EoVPUmlICnCYJIUal00qWnx5Lc2r/U0pHOjyyy0h5w/deotDhyek5qt3UaE/3RyT9JEdISaRSHVP8p3Sn845z'
        'J5WeQ/oQ1fJN9SdHTRo3Fdec8MjL87WdlKSKh08S3DPqj7hJYXjS/f6khHlefIVcB+Xh0yPq/3d8rld/otV24e96Rakz9EtQRIws'
        'd9E3NAvVt46QtnDGu3UMnHRaSXfJySd12a80pqnT4VY1epxRvGHksxNK1z1Ff8fV3wniM6mnuzlaPtPHKlyHSLYcp7rI/GshZdbi'
        '7wiue1HuXjfcvaSt7x1ZS99D1K/3qjqIN32qXqfdMuCs5GOi4puKEsclfxmocFw9PW2c14zfB0nv85RxbOSDUfQ++cXGe+pn3mP2'
        'XYq+p6iHHx7Vsj/T9V9JTeNbj15sxOzC52z/jv707+h0k88i/72cUkb872A3lr4ene2CId2lNH85bh1XMuwESQ0pGU+er/Rx4fZR'
        '3zxmGHVvVX/HwGd0N3Z8cXPocSFvPDzrRV/Bqyf1mZxBDojedXi0zqD3OSURJhrzhb7pAy1Rgx9xLfyT67GPYjb0xA48E5piAzTF'
        '/fBwPwAdsQs64qtYieTwPBf6JiNNk5OmmYBznmZjpVDom5w0zUSsUq7Fao6ITBBu0DpNgLcfqYXuaYJX5PXwEBcaqA9poL6kgZpJ'
        'A40gDdRCGmgkaaB+pIH6kwZqJf0vjfS/ANJAbaT/JRk00CzS/5Kh/yHyAml+UdD8pmnZpPmlk+aXQpppIGmmGaTz2UjniyOdL550'
        'viDS+YJJ54smnS+EdL4Y0vlCSecLc2umCfhLRN2ENh5MNGKg0DS8ETQyaXPwFwJKzYXWLageRvp5OCi/CFRYDV9kH6KdL/yQ20EL'
        'QcEIomAkKHgtKLLPTccooqMFVPwqqCPo6E90tBIdA4iO0URHG9ExhugYSHTEaih8Y8UK3AKfdT4r8TfDp8An3SeK7if9M/3e9LLp'
        'BdMzpqOmG0zXjvrbbeoxrUGa2aZSU6FpGrxV34Ov7GPwuP0aPHr3wwt5Dbya/wvezv/FS/C+gH1umgZf8Z+y50DJO+DXXwDMFlD0'
        '00TQMBnUy4UOnY811ukUD7MYvvvw3EeswjL448PDnjzr54Ci9aDfGtBtPfyQN2KlXOwga6Nddp3EfftBqVtAoWdBk+dBi9fAQx9p'
        'n4jdD+APzK3ADWInQD954Qvf+/uwBplLq5C+2mr0ztfQzz6CzvcJVh43Q85Faj74TsZHvO1HP7sFH5nqOFKdYDasVmbhU4Uc63Dd'
        'SDlPsv6RU2wnPjfhczM+h/CBns3uQ16sp0IqWLR7AONZ/H6B0r+FtMcpLdKBA1ZD639g5BTWPs/QCuhx4YkNTDLwth5YrMa1E59n'
        'IUmeB4Sb8Dk0chopT4IfvFMeNqS8lfBdR7idRg5YCvCe8Qak9EGa4+hJ2YQ3cAZfP4vv52n99VnU9ybC7VnKfZJS+AH+myx25Czg'
        'nmL5btji7XHAPibmZXgqSxMQXxs5i+dnsb4PXFHuKaof4IKah3HXh2dCBqxGqR14ez2uz+LzISBI+ALatQr305R7Lzg+CblWo44y'
        'j8T6Q+CShTpNI9xOIe8R5L0VeW8VuVCSpK6kgLw/hbZZDbz347don+dHjqn6iPL6QKV+YP/ayBmF/xmq4Rk9jaQPcomSARH8cFpI'
        'N8pzFpxzFpxzljinCle8BYyTbmqcETKWKIRnimqyZSQ3YSShVIGEYweg3YLPs/g8h8/z+LxAbXFS1Vfgfhgw7iIqmSglUoHTjlOZ'
        'J6jlOThTlmlBimPEUbJOxAcqHVqK8pl0DAlzTdnjHmN/Vfa4r5A9Lm+UPc6CXmYB3uHo+6lY11immaorV9i1uYsbG+zatGWNi+2Q'
        'eTKlD3g4DL/isbaRpZ6ZIPNC0SfjKNqOfMZRbgjKiCVJIp8xyFV/SOcYyJd0d+nCfuQHLomG3EnTclpaeobYjMm/29q29rNi+s7e'
        'DO89ljr5d093ZwtLOM93X1sPi6LvEPq29g209zKfyb8Hh1sHNdf5vvsHtc8m/6a2stK3P33b6Fva1izKdiO+A+k7gCJaCxuo7ygr'
        'aIS51He3L85K9PmhKR37ETh2TVzLW7EH6Cbs0YrB7oyntN1aA1l8JFQO2vvAlvuQ+JAlFv1Ie41VeWxvaC+OtrSKt6wI3JlG6Tap'
        'O66tw8jugZegBWAnxt+wB+MN7Jb4DXZX/AH7Kv7ETwvMYY/6OXZovI79F7/GzovfY8/F2/zP7tzMdDnZg3VYmdjDMi4szy4MpAwZ'
        'H6pnD4cHPmgq4IdCP8nCbqzHsQfrSfZd7Jn6gwHCh9jvccZQ/2JxKBy43kYUeAa98jTdPU13XFg8ySKejx1gHHv0mJCZAjq1IAe3'
        'U7RwjJ8iArnsl+FEuX7QWbyJG/PGB+Mk7Hewyn1mtINiV6IvRty56KcJmji/zYcLa30R+wfdM3UvWlVYwekX9mSJ698I58/p/q+A'
        'mIpSw7C2NqJSnZOp2FmZgv2LrmfIRvox7fyCddDQNjWa2sml7+LiEbR7C/usDKmSkMo0zh4w7M4StmRZP7E/CzQyUksjnhNaSQRB'
        'C6N2W6fexNHTOM8b4kTmxYfga+127WvYQzhE/Hordrh1s0EqxR97CFcwse57Byz+G0DRGGqHVEM7iBPzzOAsI5eawY0efoYnA+K9'
        'C479uTuPiSAwaILyiWgjX+Lf34jdQ/S+3lBKMFlp3xUWdXpX4PUOkmAi3iYuI9s10YRBS5Mla6RlBo7K9zuvnIz9gUqzG0oLIkzd'
        'eQTl1Z4qD5Txd0p96q51oQGWD3sMexyfYE8p/BK88DOpXgaaGvuhgdNLcZ+HFomR0Mgf5R26e99995777l33ncLXYPMWnyCq9Z9F'
        'KvYnxWkFitMY/AcEt5Uq7ISPw1EOCzz/Dn+SJO1o/EWb3Y8T40n6Clmi0oiSssEFj5C3yV3wMrkJ+q/Rq0T3JBEy6C+qXwm7+6dy'
        'NyXtVPS0AQfX/A++P+G/wvcb2NPGwUtCK/kbfxXfs0UvQo9z4DuKwwKPHoj1ePREK77DOc45QM9Eb0APxaiMnopTW9BjffEdhPMh'
        'OHqwyatPJ9M4IPrNg9hnnI1xAf1Hb0nsTf0Fe8vYBwy74T7CrOOvNEMVIwh6G0YRIWWrRK8bJWtfHk9KK47Q/g/77lVc'
    )),
}


if __name__ == "__main__":
    logging.basicConfig(level=logging.INFO,
                        format="%(asctime)s %(levelname)s [%(threadName)s] %(message)s")
    logging.info("Build: %s", BUILD)
    register_prompt_fonts()
    app = AntiTriggerFingersApp()
    app.mainloop()
