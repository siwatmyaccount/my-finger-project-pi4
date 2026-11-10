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
import glob
import base64
import shutil
import subprocess
import tempfile
from tkinter import filedialog, messagebox


THAI_MONTHS = ("", "มกราคม", "กุมภาพันธ์", "มีนาคม", "เมษายน", "พฤษภาคม", "มิถุนายน",
               "กรกฎาคม", "สิงหาคม", "กันยายน", "ตุลาคม", "พฤศจิกายน", "ธันวาคม")
UI_LANGUAGE = "th"


def ui(thai, english):
    return english if UI_LANGUAGE == "en" else thai


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
            "ทำครบแล้ว ครั้งหน้าลองขยับช้า ๆ และพักเมื่อเมื่อย", "You finished. Move slowly and rest when tired.")
    return ui("หยุดพักหลายช่วง", "Several pauses"), "#C0392B", ui(
        "ทำครบแล้ว แต่มีช่วงที่ต้องหยุดบ่อย ลองจัดมือให้อยู่ในภาพและพักเมื่อเมื่อย",
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
        self._localized_labels = []
        self._last_feedback = ("💬 รอตรวจจับท่าทาง...", "Show your hand", "#7F8C8D")
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
        self._report_started_at = datetime.now().astimezone()
        self._last_report_expiry_check = time.monotonic()
        self._last_live_report_update = 0.0
        self._last_pain = None
        self._pain_before = None
        self._pain_after = None
        self._load_report_state()
        self._prune_activity_log()
        self._save_report_state()
        self.set = len(self.completed_sets)
        self._set_stable_poses = 0
        self._pose_had_long_pause = False
        self._pose_pause_started = None
        self._daily_pose_cache_time = 0.0
        self._daily_pose_counts = []
        self._goal_reached = self.set >= self.target_sets_var.get()
        

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

        self.font_large_title = ("Sarabun", max(26, int(32 * self.u_scale)), "bold")
        self.font_medium_text = ("Sarabun", max(21, int(30 * self.u_scale)), "bold")
        self.font_timer = ("Sarabun", max(50, int(55 * self.u_scale)), "bold")
        self.font_pose_title = ("Sarabun", max(27, int(28 * self.u_scale)), "bold")
        self.font_pose_action = ("Sarabun", max(22, int(25 * self.u_scale)), "bold")
        self.font_btn_text = ("Sarabun", max(23, int(22 * self.u_scale)), "bold")
        self.font_small = ("Sarabun", max(19, int(18 * self.u_scale)), "bold")
        self.font_feedback = ("Sarabun", max(20, int(18 * self.u_scale)), "bold")

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
            self.logo_label = ctk.CTkLabel(self.top_bar_frame, text="LOGO", font=("Sarabun", 18, "bold"), text_color=self.white_fg)
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
            self.camera_label, text="กำลังหามือ", font=("Sarabun", max(21, int(24 * self.u_scale)), "bold"), 
            fg_color="#FFFFFF", text_color="#E74C3C", corner_radius=6, padx=10, pady=2
        )
        self.match_badge.place(x=15, y=15)
        
        self.env_badge = ctk.CTkLabel(
            self.camera_label, text="ระยะกล้อง/แสง: ตรวจสอบ...", font=("Sarabun", max(17, int(18 * self.u_scale)), "bold"),
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
        
        self.Label_set_text = ctk.CTkLabel(self.sets_line_frame, text="เซ็ตที่ : ", font=self.font_medium_text, text_color=self.black_fg)
        self._localized_labels.append((self.Label_set_text, "เซ็ตที่ : ", "Set: "))
        self.Label_set_text.pack(side="left", padx=(14, 0))
        self.Label_set_number = ctk.CTkLabel(self.sets_line_frame, text=f"{self.set}", font=self.font_medium_text, text_color=self.green_btn)
        self.Label_set_number.pack(side="left", padx=(0, 14))

        self.round_progress = ctk.CTkProgressBar(self.set_times_frame, width=int(280 * self.scale_w), height=14, fg_color="#EAECEE", progress_color=self.green_btn, corner_radius=8)
        self.round_progress.pack(pady=(2, 4))
        self.round_progress.set(0) 
        
        self.reward_label = ctk.CTkLabel(self.set_times_frame, text="พร้อมแล้ว เริ่มฝึกได้", font=("Sarabun", max(19, int(20 * self.u_scale)), "bold"), text_color="#A45C00")
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

        self.pose_feedback_label = ctk.CTkLabel(self.pose_text_frame, text="💬 รอตรวจจับท่าทาง...", font=self.font_feedback, text_color="#52667A", wraplength=center_wrap)
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
        
        self.pain_title = ctk.CTkLabel(self.pain_frame, text="ความปวดของมือ (0-10)", font=("Sarabun", max(19, int(20 * self.u_scale)), "bold"), text_color="#9C4300")
        self.pain_title.pack(pady=(4, 0))
        self._localized_labels.append((self.pain_title, "ความปวดของมือ (0-10)", "Hand pain (0-10)"))
        
        slider_inner = ctk.CTkFrame(self.pain_frame, fg_color="transparent")
        slider_inner.pack(fill="x", padx=10, pady=(0, 4))
        
        self.pain_var = ctk.IntVar(value=5)
        self.pain_val_lbl = ctk.CTkLabel(slider_inner, text="5", font=("Sarabun", 22, "bold"), text_color="#A22B20", width=35)
        self.pain_val_lbl.pack(side="left", padx=(2, 6))
        
        self.pain_slider = ctk.CTkSlider(slider_inner, from_=0, to=10, number_of_steps=10, variable=self.pain_var, command=lambda v: self.pain_val_lbl.configure(text=int(v)), progress_color="#E74C3C", button_color="#C0392B", height=22, width=80)
        self.pain_slider.pack(side="left", fill="x", expand=True, padx=4)
        
        self.pain_btn = ctk.CTkButton(slider_inner, text="บันทึก", font=self.font_small, fg_color="#B83228", hover_color="#8C251E", width=90, height=max(40,int(48 * self.scale_h)), command=self.save_pain_log)
        self.pain_btn.pack(side="right", padx=(8, 2))

        self.controls_btn_frame = ctk.CTkFrame(self.center_info_container, fg_color="transparent")
        self.controls_btn_frame.place(rely=.82, relwidth=1, relheight=.172)
        self.controls_btn_frame.pack_propagate(False)
        
        self.start_stop_button = ctk.CTkButton(
            self.controls_btn_frame, text="ดูผลการฝึก" if self._goal_reached else "▶ เริ่มต้น", font=self.font_btn_text, fg_color=self.green_btn,
            text_color=self.white_fg, command=lambda: self.toggle_start_pause(), height=self.btn_h,
            hover_color=self.hover_green_bt, corner_radius=15
        )
        self.start_stop_button.place(relwidth=1, relheight=.47)
        
        self.reset_button = ctk.CTkButton(
            self.controls_btn_frame, text="🔄 รีเซ็ต", font=self.font_btn_text, fg_color=self.red_btn,
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

        self.breathing_label = ctk.CTkLabel(self.timer_frame, text="เตรียมพร้อมหายใจ...", font=("Sarabun", max(19,int(20 * self.u_scale)), "bold"), text_color="#52667A", wraplength=int(self.screen_width * .30) - 28)
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
            self.small_hand_label = ctk.CTkLabel(self.small_hand_bg, text="รูปตัวอย่าง", font=("Sarabun", 16), width=img_size, height=img_size)
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
        self.report_title = ctk.CTkLabel(self.analysis_card, text="ผลการฝึกและความสบายของมือ", font=("Sarabun", max(26, int(30 * self.u_scale)), "bold"), text_color=self.black_fg)
        self.report_title.pack(pady=(12, 0))
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
                                            font=("Sarabun", max(24, int(28 * self.u_scale)), "bold"), text_color=self.black_fg,
                                            wraplength=gauge_width, justify="center")
        self.report_progress.pack(pady=(0, 4))
        self.report_guidance = ctk.CTkLabel(self.gauge_column, text="เริ่มฝึกที่หน้าหลัก เมื่อทำได้แม้เพียง 1 ท่ากลับมาดูผลได้",
                                            font=("Sarabun", max(20, int(23 * self.u_scale))), text_color="#52667A",
                                            wraplength=gauge_width, justify="center")
        self.report_guidance.pack(padx=6, pady=(0, 8))

        self.report_info = ctk.CTkFrame(self.report_body, fg_color="transparent")
        self.report_info.place(relx=.56, relwidth=.44, rely=.008, relheight=.984)
        report_wrap = int(self.screen_width * .32) - 36
        report_title_font = ("Sarabun", max(21, int(26 * self.u_scale)), "bold")
        report_value_font = ("Sarabun", max(23, int(30 * self.u_scale)), "bold")
        report_detail_font = ("Sarabun", max(17, int(23 * self.u_scale)))

        self.comfort_card = ctk.CTkFrame(self.report_info, fg_color="#F5EFF8",
                                        border_width=1, border_color="#DDCDE6", corner_radius=16)
        self.comfort_card.place(relwidth=1, relheight=.49)
        self.comfort_title = ctk.CTkLabel(self.comfort_card, font=report_title_font, text_color="#FFFFFF",
                                          fg_color=self.purple_bg, corner_radius=9)
        self.comfort_title.place(relx=.035, rely=.045, relwidth=.93, relheight=.20)
        self._localized_labels.append((self.comfort_title, "ความสบายของมือ", "Hand comfort"))
        self.report_pain_change = ctk.CTkLabel(self.comfort_card, font=report_value_font,
                                               wraplength=report_wrap, justify="center")
        self.report_pain_change.place(rely=.27, relwidth=1, relheight=.27)
        self.report_pain = ctk.CTkLabel(self.comfort_card, font=report_detail_font,
                                       text_color=self.black_fg, justify="center", wraplength=report_wrap)
        self.report_pain.place(rely=.55, relwidth=1, relheight=.40)

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
        self.actions_title = ctk.CTkLabel(self.report_actions, text="เลือกสิ่งที่ต้องการ", font=("Sarabun", max(22, int(24 * self.u_scale)), "bold"), text_color=self.black_fg)
        self.actions_title.pack(pady=(18, 12))
        self._localized_labels.append((self.actions_title, "เลือกสิ่งที่ต้องการ", "Actions"))

        self.export_button = ctk.CTkButton(
            self.report_actions, text="ส่งออกข้อมูล", font=self.font_btn_text,
            fg_color="#137A4B", text_color="#FFFFFF", hover_color="#0C5F39",
            command=self.export_completed_sets, height=max(68, int(105 * self.scale_h)), corner_radius=14)
        self.export_button.pack(side="top", fill="x", padx=8, pady=10)
        self.export_note = ctk.CTkLabel(self.report_actions, text="เฉพาะเซตที่ทำเสร็จ", font=("Sarabun", 18, "bold"), text_color="#43566A")
        self.export_note.pack(pady=(0, 4))
        self._localized_labels.append((self.export_note, "เฉพาะเซตที่ทำเสร็จ", "Completed sets only"))

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
            self.goal_popup, text="สุดยอดมาก! 🎉\nคุณทำครบเป้าหมายที่ตั้งไว้แล้ว!", 
            font=("Sarabun", int(26 * self.u_scale), "bold"), text_color="#B7950B", justify="center"
        )
        self.goal_popup_label.pack(padx=25, pady=20)

        self.config_popup = ctk.CTkFrame(self, fg_color="#FFFFFF", corner_radius=15, border_width=2, border_color=self.purple_bg)
        
        self.config_popup_header = ctk.CTkFrame(self.config_popup, fg_color="transparent")
        self.config_popup_header.pack(fill="x", padx=15, pady=(12, 6))
        
        self.config_popup_title = ctk.CTkLabel(self.config_popup_header, text="เลือกการตั้งค่า", font=("Sarabun", 22, "bold"), text_color=self.purple_bg)
        self.config_popup_title.pack(side="left", padx=5)
        
        self.config_close_btn = ctk.CTkButton(
            self.config_popup_header, text="✕", font=("Arial", 20, "bold"), fg_color="#C0392B", text_color="#FFFFFF",
            hover_color="#992D22", width=40, height=40, corner_radius=20, command=self.close_config_popup
        )
        self.config_close_btn.pack(side="right", padx=5)

        self.config_options_container = ctk.CTkFrame(self.config_popup, fg_color="transparent")
        self.config_options_container.pack(padx=25, pady=(0, 20), fill="x", anchor="center")

        self.update_idletasks() 
        self.attributes("-fullscreen", True)

        self.refresh_language()
        voice_worker = threading.Thread(target=self._voice_loop, name="voice", daemon=True)
        self._workers.append(voice_worker)
        voice_worker.start()
        self.check_sensor_loop()
        self.protocol("WM_DELETE_WINDOW", self.on_close)
        self._video_job = self.after(0, self._start_video)

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
        if UI_LANGUAGE == "en" and not self._voice_warning_shown and not shutil.which("mpg123"):
            self._voice_warning_shown = True
            messagebox.showwarning("Voice unavailable", "On the Pi, install the audio player: sudo apt install mpg123")
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
        self.pain_btn.configure(text=ui("บันทึก! ✅", "Saved! ✅") if self._pain_button_saved
                                else ui("บันทึก", "Save"))
        self.start_stop_button.configure(text=ui("ดูผลการฝึก", "View results") if self._goal_reached
                                         else ui("⏸ หยุด", "⏸ Pause") if self.running or self.countdown_active
                                         else ui("▶ เริ่มต้น", "▶ Start"))
        self.reset_button.configure(text=ui("🔄 รีเซ็ต", "🔄 Reset"))
        self.log_button.configure(text=ui("ผลการฝึกของฉัน", "My results"))
        self.export_button.configure(text=ui("ส่งออกข้อมูล", "Export results"))
        self.report_reset_button.configure(text=ui("รีเซ็ตผลการฝึก", "Reset results"))
        self.next_advice_button.configure(text=ui("คำแนะนำ", "Practice tips"))
        self.back_button.configure(text=ui("กลับหน้าหลัก", "Home"))
        self.config_popup_title.configure(text=ui("🖐️ เลือกมือที่ต้องการฝึก", "🖐️ Choose a hand"))
        self.goal_popup_label.configure(text=ui("สุดยอดมาก! 🎉\nคุณทำครบเป้าหมายที่ตั้งไว้แล้ว!",
                                                "Well done! 🎉\nYou finished your practice goal!"))
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
        for widget in self.config_options_container.winfo_children():
            widget.destroy()
        self.config_popup_title.configure(text=ui("🖐️ เลือกมือที่ต้องการฝึก", "🖐️ Choose a hand"))
        
        for h_val in ["ซ้าย", "ขวา"]:
            b = ctk.CTkButton(
                self.config_options_container, text=hand_label(h_val), font=("Sarabun", 20, "bold"), height=60, width=280,
                fg_color=self.purple_bg if self.target_hand_var.get() == h_val else "#E5E7E9",
                text_color=self.white_fg if self.target_hand_var.get() == h_val else self.black_fg,
                hover_color="#5B2C6F", corner_radius=12, anchor="center",
                command=lambda val=h_val: self.select_hand(val)
            )
            b.pack(pady=10, anchor="center")
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

    def trigger_goal_popup(self, target):
        msg = ui(f"ทำครบเป้าหมาย {target} เซตแล้ว! 🎉\nกดดูผลการฝึกหรือส่งออกผลได้",
                 "Well done! Set complete.\nTap View results to see your progress.")
        self.goal_popup_label.configure(text=msg)
        self.goal_popup.place(relx=0.5, rely=0.5, anchor="center")
        self.goal_popup.tkraise()
        self.after(3500, self.goal_popup.place_forget)

    def save_pain_log(self):
        val = self.pain_var.get()
        self._last_pain = val
        if self.set == 0 and self.round == 0 and self.current_pose == 1:
            self._pain_before = val
            self.write_log(f"PainBefore: {val}")
        else:
            self._pain_after = val
            self.write_log(f"PainAfter: {val}")
        if self.history_page.winfo_ismapped():
            self.update_live_report()
        self._save_report_state()
        self._pain_button_saved = True
        self.pain_btn.configure(text=ui("บันทึก! ✅", "Saved! ✅"), fg_color=self.green_btn)
        self.after(2000, self.reset_pain_button)
        if UI_LANGUAGE == "en":
            self._queue_voice("012.mp3")

    def reset_pain_button(self):
        self._pain_button_saved = False
        self.pain_btn.configure(text=ui("บันทึก", "Save"), fg_color="#E74C3C")

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
        target = max(1, self.target_sets_var.get())
        partial = self.round * 5 + self.current_pose - 1
        done = self.set * 15 + partial
        total = max(target, self.set) * 15
        if done == 0:
            status, color = ui("พร้อมเริ่มฝึก", "Ready to begin"), "#8191A1"
            guidance = ui("เริ่มฝึกที่หน้าหลัก เมื่อทำได้แม้เพียง 1 ท่ากลับมาดูผลได้",
                          "Tap Start on the home screen.")
        elif self.set * 3 + self.round >= 3:
            status, color = ui("ทำครบแล้ว", "Set complete"), "#137A4B"
            guidance = ui("ทำครบ 3 รอบแล้ว · พักมือเมื่อเมื่อย", "Three rounds complete.")
        elif self.set * 3 + self.round >= 1:
            status, color = ui("กำลังฝึก", "In progress"), "#A56A00"
            guidance = ui("ทำครบแล้วอย่างน้อย 1 รอบ · ค่อย ๆ ทำต่อเมื่อพร้อม", "Keep going when you’re ready.")
        else:
            status, color = ui("กำลังเริ่ม", "Getting started"), "#B83228"
            guidance = ui("ยังไม่ครบ 1 รอบ · ทำต่อเมื่อพร้อมและพักเมื่อเมื่อย", "Finish the first round when ready.")
        size = self.gauge_size
        pad = max(14, size // 14)
        width = max(13, size // 15)
        self.gauge.delete("all")
        self.gauge.create_oval(pad, pad, size-pad, size-pad, outline=color, width=width)
        self.gauge.create_text(size/2, size*.43, text=status, fill=color,
                               font=("Sarabun", max(23, int(32*self.u_scale)), "bold"), width=size*.77)
        self.gauge.create_text(size/2, size*.61, text=ui(f"{done} ท่า", f"{done} poses"), fill=self.black_fg,
                               font=("Sarabun", max(38, int(50*self.u_scale)), "bold"))
        self.report_progress.configure(text=ui(
            f"ทำแล้ว {done} จาก {total} ท่า · ครบ {self.set*3 + self.round} รอบ · {self.set} เซต",
            f"{done}/{total} poses · {self.set*3 + self.round}/3 rounds" if self.set <= 1
            else f"{done}/{total} poses · {self.set} sets"))
        self.report_guidance.configure(text=guidance)
        before = pain_description(self._pain_before)
        after = pain_description(self._pain_after)
        self.report_pain.configure(text=ui(f"ก่อนฝึก: {before}\nหลังฝึก: {after}",
                                           f"Before: {before}\nAfter: {after}"))
        if self._pain_before is not None and self._pain_after is not None:
            if self._pain_after > self._pain_before:
                pain_text, pain_color = ui("ปวดมากขึ้น", "More pain"), "#B83228"
            elif self._pain_after < self._pain_before:
                pain_text, pain_color = ui("ปวดลดลง", "Less pain"), "#137A4B"
            else:
                pain_text, pain_color = ui("ปวดเท่าเดิม", "No change"), "#52667A"
        else:
            pain_text, pain_color = ui("ก่อนและหลังฝึก", "Before & after"), "#52667A"
        self.report_pain_change.configure(text=pain_text, text_color=pain_color)
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

    def show_next_advice(self):
        if getattr(self, "advice_popup", None) is not None and self.advice_popup.winfo_exists():
            self.advice_popup.lift()
            return
        completed_rounds = self.set * 3 + self.round
        partial = self.current_pose - 1
        if completed_rounds == 0 and partial == 0:
            message = ui("ให้มืออยู่ในภาพกล้อง\nค่อย ๆ ทำตามรูปตัวอย่าง",
                         "Keep your hand in view.\nFollow the example at your own pace.")
        elif completed_rounds < 3:
            next_round = 5 - partial
            remaining_rounds = 3 - completed_rounds
            message = ui((f"รอบนี้เหลือ {next_round} ท่า\n"
                          f"เซตนี้เหลือ {remaining_rounds} รอบ\n"
                          "พักได้เมื่อมือเมื่อย"),
                         (f"This round: {next_round} {'pose' if next_round == 1 else 'poses'} left.\n"
                          f"This set: {remaining_rounds} {'round' if remaining_rounds == 1 else 'rounds'} left.\n"
                          "Rest if your hand feels tired."))
        else:
            message = ui("ทำครบ 1 เซตแล้ว พักมือได้\nหากต้องการเริ่มใหม่ กดรีเซ็ตผลการฝึก",
                         "Set complete. Time to rest.\nTap Reset results to start over.")
        popup = ctk.CTkToplevel(self)
        self.advice_popup = popup
        popup.title(ui("คำแนะนำครั้งถัดไป", "Practice tips"))
        popup.configure(fg_color="#FFFFFF")
        width = min(760, max(480, int(self.screen_width * .68)))
        height = min(430, max(330, int(self.screen_height * .60)))
        popup.resizable(False, False)
        popup.geometry(f"{width}x{height}+{(self.screen_width-width)//2}+{(self.screen_height-height)//2}")
        popup.transient(self)
        popup.lift()
        ctk.CTkLabel(popup, text=ui("คำแนะนำครั้งถัดไป", "Practice tips"), font=("Sarabun", 32, "bold"),
                     text_color=self.purple_bg).pack(pady=(25, 12))
        ctk.CTkLabel(popup, text=message, font=("Sarabun", 30, "bold"),
                     text_color=self.black_fg, wraplength=width-60, justify="center").pack(fill="both", expand=True, padx=25)
        ctk.CTkButton(popup, text=ui("เข้าใจแล้ว", "OK"), font=("Sarabun", 27, "bold"),
                      fg_color=self.purple_bg, text_color="#FFFFFF", command=popup.destroy,
                      height=65, width=230).pack(pady=(8, 22))
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

    def export_completed_sets(self):
        if not self.completed_sets:
            messagebox.showinfo(ui("ยังส่งออกไม่ได้", "No completed sets"),
                                ui("ทำครบอย่างน้อย 1 เซตก่อนจึงจะส่งออกได้", "Finish at least one set first."))
            return
        stamp = datetime.now().strftime("%Y-%m-%d_%H-%M")
        path = filedialog.asksaveasfilename(
            parent=self, title=ui("บันทึกผลการฝึกเพื่อนำไปส่งต่อ", "Save practice results to share"),
            defaultextension=".txt", initialfile=ui(f"ผลการฝึก_{stamp}.txt", f"practice_results_{stamp}.txt"),
            filetypes=[(ui("ไฟล์ข้อความ", "Text file"), "*.txt")])
        if not path:
            return
        lines = [ui("ผลการฝึกบริหารนิ้ว", "Finger exercise results"),
                 ui("เฉพาะเซตที่ทำเสร็จก่อนกดรีเซ็ต", "Completed sets before reset only"), ""]
        for item in self.completed_sets:
            title, _, advice = assess_completed_set(item["stable_poses"])
            lines.extend([
                ui(f"เซตที่ {item['set_number']}: {thai_datetime(datetime.fromisoformat(item['completed_at']))}",
                   f"Set {item['set_number']}: {thai_datetime(datetime.fromisoformat(item['completed_at']))}"),
                ui(f"มือที่ฝึก: {item['hand']} | ทำครบ: {item['total_poses']} ท่า (3 รอบ)",
                   f"Hand: {hand_label(item['hand'])} | Completed: {item['total_poses']} poses (3 rounds)"),
                ui(f"เวลาค้างท่าที่ตั้ง: {item['hold_seconds']} วินาทีต่อท่า",
                   f"Hold time: {item['hold_seconds']} seconds per pose"),
                ui(f"ความต่อเนื่องที่กล้องตรวจพบ: {item['stable_poses']}/15 ท่า | ผล: {title}",
                   f"Steady camera tracking: {item['stable_poses']}/15 poses | Result: {title}"),
                (ui(f"ระดับความปวดที่บันทึก: {item['pain']}/10", f"Reported pain: {item['pain']}/10")
                 if item.get('pain') is not None else ui("ระดับความปวด: ไม่ได้บันทึก", "Pain: not recorded")),
                ui(f"คำแนะนำ: {advice}", f"Advice: {advice}"), improvement_tip(item["stable_poses"]), ""])
        lines.append(ui("ผลสีประเมินความต่อเนื่องของการตรวจจับ ไม่ใช่ผลวินิจฉัยทางการแพทย์",
                        "Colours show camera tracking continuity, not a medical diagnosis."))
        try:
            with open(path, "w", encoding="utf-8-sig") as output:
                output.write("\n".join(lines) + "\n")
        except OSError as exc:
            logging.exception("Export failed: %s", exc)
            messagebox.showerror(ui("บันทึกไม่สำเร็จ", "Save failed"),
                                 ui("ตรวจตำแหน่งและสิทธิ์บันทึกไฟล์ แล้วลองใหม่",
                                    "Check the save location and permissions, then try again."))
            return
        if UI_LANGUAGE == "en":
            self._queue_voice("014.mp3")
        messagebox.showinfo(ui("ส่งออกสำเร็จ", "Export complete"),
                            ui(f"บันทึกไฟล์แล้ว:\n{path}\nนำไฟล์นี้ไปส่งต่อได้",
                               f"Saved:\n{path}\nYou can share this file."))

    def _queue_voice(self, filename):
        with self._voice_condition:
            if self._voice_stopping:
                return
            self._voice_revision += 1
            self._voice_pending = (filename, UI_LANGUAGE, self._voice_revision) if filename else None
            self._voice_condition.notify()

    def _voice_loop(self):
        while True:
            with self._voice_condition:
                self._voice_condition.wait_for(lambda: self._voice_pending or self._voice_stopping)
                if self._voice_stopping:
                    return
                filename, language, revision = self._voice_pending
                self._voice_pending = None

            player = shutil.which("mpg123")
            if not player:
                logging.warning("Voice playback requires mpg123")
                continue
            try:
                if language == "en":
                    with tempfile.TemporaryFile() as stream:
                        stream.write(base64.b64decode(ENGLISH_VOICE_CLIPS[filename]))
                        stream.seek(0)
                        self._play_voice([player, "-q", "-"], revision, stream)
                else:
                    path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "Voices", filename)
                    if os.path.isfile(path):
                        self._play_voice([player, "-q", path], revision)
                    else:
                        logging.warning("Thai audio file missing: %s", path)
            except (OSError, KeyError, subprocess.SubprocessError):
                logging.exception("Voice playback failed for %s", filename)

    def _play_voice(self, command, revision, source=None):
        with self._voice_condition:
            if self._voice_revision != revision:
                return
        with subprocess.Popen(command, stdin=source, stdout=subprocess.DEVNULL,
                              stderr=subprocess.DEVNULL) as process:
            deadline = time.monotonic() + 20
            while process.poll() is None:
                with self._voice_condition:
                    changed = self._voice_condition.wait_for(
                        lambda: self._voice_revision != revision, timeout=.05)
                if changed or time.monotonic() >= deadline:
                    process.terminate()
                    try:
                        process.wait(timeout=.3)
                    except subprocess.TimeoutExpired:
                        process.kill()
                    return
            if process.returncode:
                logging.warning("Audio player exited with code %s", process.returncode)

    def show_main_page(self):
        self.history_page.pack_forget()
        self.main_content_frame.pack(side="top", fill="both", expand=True, padx=8, pady=4)
        self._queue_voice(self.pose_sounds[self.current_pose][0] if self.running else "010.mp3")

    def show_history_page(self):
        self.main_content_frame.pack_forget()
        self._queue_voice("009.mp3")
        self.history_page.pack(side="top", fill="both", expand=True)
        self.update_set_analysis()

    def write_log(self, message):
        now = datetime.now().strftime("[%Y-%m-%d %H:%M:%S]")
        log_message = f"{now} เซ็ตที่ {self.set} รอบที่ {self.round} : {message}"
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
        self.set_feedback("💬 ลุยท่าต่อไปได้เลย!", "Ready for the next pose", "#F39C12")

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
            reward_msg = ui("🌟 พร้อมแล้ว เริ่มลุยเลย!", "Ready to start")
            color = "#F39C12"
        elif self.round == 0 and self.set > 0:
            reward_msg = ui(f"🏆 สุดยอด! จบเซ็ตที่ {self.set} แล้ว!",
                            f"Set {self.set} complete")
            color = "#27AE60"
        else:
            reward_msg = ui(f"🔥 ลุยต่อ! (เซ็ตที่ {self.set + 1}/{target} | รอบที่ {self.round}/3)",
                            f"Rounds done: {self.round}/3")
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

    def toggle_start_pause(self):
        if self._goal_reached:
            self.show_history_page()
            return
        if not self.running and not self.countdown_active:
            self.start_stop_button.configure(text=ui("⏸ หยุด", "⏸ Pause"), fg_color=self.yellow_btn, hover_color=self.hover_yellow_bt)
            self.start_pose_countdown(2)
            self._queue_voice("006.mp3")
        else:
            self.start_stop_button.configure(text=ui("▶ เริ่มต้น", "▶ Start"), fg_color=self.green_btn, hover_color=self.hover_green_bt)
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
                self._queue_voice(self.pose_sounds[self.current_pose][0])
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
        if confirm and (self.completed_sets or self.round or self.current_pose > 1) and not messagebox.askyesno(
                ui("เริ่มบันทึกใหม่", "Start a new record"),
                ui("ผลการฝึกบนหน้าจอจะถูกล้าง\nต้องการเริ่มใหม่หรือไม่?",
                   "Practice results on this screen will be cleared.\nStart again?")):
            return
        self.running = False
        try:
            self._cancel_countdown()
        except Exception:
            pass
        self.start_stop_button.configure(text=ui("▶ เริ่มต้น", "▶ Start"), fg_color=self.green_btn, hover_color=self.hover_green_bt)
        self.round = 0
        self.set = 0
        self.completed_sets.clear()
        self._set_stable_poses = 0
        self._pose_had_long_pause = False
        self._pose_pause_started = None
        self._last_pain = None
        self._pain_before = None
        self._pain_after = None
        self._goal_reached = False
        self._report_started_at = datetime.now().astimezone()
        self._clear_report_storage()
        self._daily_pose_counts = []
        self._daily_pose_cache_time = 0.0
        self._save_report_state()
        self.update_set_analysis()
        self.current_pose = 1
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
        self.set_hand_posit_state(False)
        self._stop_video.set()
        with self._voice_condition:
            self._voice_stopping = True
            self._voice_revision += 1
            self._voice_condition.notify()
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
                self.set_breathing("⏸ พักเวลาไว้ · จัดมือใหม่เมื่อพร้อม",
                                   "Paused · adjust your hand", "#E74C3C")

        try:
            self._sensor_job = self.after(100, self.check_sensor_loop)
        except Exception:
            pass

    def _on_pose_success(self):
        if not self._pose_had_long_pause:
            self._set_stable_poses += 1
        self._pose_had_long_pause = False
        self._pose_pause_started = None
        try:
            completed_pose_name = self.pose_name[self.current_pose]
            self.write_log(f"ท่า {completed_pose_name} สำเร็จ! 🌟")
            
            encouragements = [("เก่งมาก! 👏", "Well done! 👏"), ("ยอดเยี่ยม! 🌟", "Excellent! 🌟"),
                              ("เป๊ะมาก! ✨", "Great work! ✨"), ("สุดยอด! 🔥", "You did it! 🔥")]
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
                self._goal_reached = True
                self.running = False
                self.start_stop_button.configure(text=ui("ดูผลการฝึก", "View results"), fg_color=self.green_btn)
                self.trigger_goal_popup(1)

        try:
            self.update_round()
            self.timer_reset()
            self.update_EX_pose()
            self.update_text()
            self.after(2500, self.reset_feedback)
            
            if self._goal_reached:
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
        '//NQxAARQH6Ft0MQAKCAAJ9Ou3+u5/Hc37XcAAAAQiFXAAAAAAQlAwUBD9YPg+//ggGP+oEHfOfWHwQBAEDhc/3cuf8E'
        'DlP/lw+kEOXP/o//k4kyGQiARIpJIWzIpFIcn0xWngOxrQQ0+H1Bkn5DK4Dh85zbOPcxJEzGMXAALhJhy//zUsQwJYOS'
        'wl+YaAIlFxEFAlhQHAeHQkC6bGxYZMSDLPHFIougg2m6i4g6nRMS+XHc67CXkDuo0M9B2Oj2RUcQzcvk0uOkxflw+X3W'
        'ZoIt/3Uqy6vpunrT//+///7//7s/3S//05umpZogaAPvhgQEBg3MgABO6tu6un1GvlhN0uLT//NSxBAec+bmX884Ao+Y'
        'InogTlG3mE+VE3+aKoTkWQ5xJXRDgKGGVHh8urspiqtLL5v0+jmvlh0iSEggYeacaTPPc08oYYRIot6/5rmMzJaabX//'
        '//9f/0Z9FNJno5QcFxAxzSpYX/////t1HxY7qehjcw8m2IHVAUx2/tzaSsu3lmD/81DEDBxTquJeecrmN4GUBTifNkiC'
        'ZfBAm9P/oUaivZsQRHQCrLkiwTm8PAwZ6hAfNiLF0UpRVXdBIPf35jOKaB4WAZXR2mtEgMcOvKdEN/OpUt1/////+v/9'
        'P2H1tGkpUxm6ao6o/WxvVV0xxnQ7lQVVhADDUv0T2lufG92oSAJq//NSxA8c477KXniLOm3XK8W2GYu6VowoTO9evy9o'
        'OFNj9jWpIv/DBRJmlIcBTcDDCXVm0uuT2+VAtHSYhAIUv8MiKAtL/4Uau9Jn+y/+n+pbFW3/9H/T3UOirasHgMZSymMY'
        'xjPMpW36fKyNoHhw6d71AD28M32//lWjbHVBmtK2yKr/81LEERzhopB+wkUEv+OiTnBY68s+LT1GlZas1NqArGlvPy0J'
        'yTMVzFF4IYtUqQErmLCvUpkzFvT9tJ0FFBDBhnuUvZEAh4swtDhyUlUBM8m9O3JMN7aGxbtTdWFFGirnOd9NAu9+lY1b'
        '0Mf3rLa1ZAKlhSkkH/j2zJJay2f3VxnxU//zUMQTGKGimR9YOAIy6G7FPc4v+KTmsOQsJBJFhNoUB213QuIo+t2jgnc1'
        '8+57VWfa5n/9TSY4cNTS49lrrebHW1eoP73HjKOhm2LVe5CaHLjfuGWpSHdTn6kxdU0nCoia3JLLZZbJAGAPt9Sfzh0e'
        'W8AIE75wercm7RNIjatxaon/81LEJSPLGqpfmIAC8QwwErIqbkBGKXAOxfhjAdxDx5E6E0Xkjilm5ydKDOV3QRRTTUhR'
        'IYUy+gupJM8bENrU9bF8xOmKlpGpMm6zxskqVk0idTPl1pEDc2Jh3Tc2+tG/q7L/smfWbm7J1pq/////79tqDOzJGiqG'
        'BARSGmACiCD5Xv/zUMQLHFMmvZWYOAClObMJ+LtaVEBowDQv3IYfHTt+VOuN4nQ80oaYxI+aGCY0REKOwmFomXzGTA8i'
        'C89/dvPPXKDUbgBs//5kxrMrVKg/Qw9EVEV3b7f+0/NX+7bHzD1nnlDf////pPHTiBk4XFnf/+NqeCQESGU5HZhNc1rg'
        'ux3/81LEDhqB6tsfz0AAYR5rYGJqeNqKRyejahqeX/GMuw64vtm/0ta/kYLX+SIIit9XP8OKBFU8lANFBY6yBKJR1XZp'
        'wqK3XZosdrMCUPVjVmVagag9W4c0GqRK7////K+Vilbo5/93yxKgG6uFcCPN4ZyhsJlWyKcqymRNVGiLN3G0+//zUsQa'
        'F4oOsZbKBPKLAL23NfTxFiCqr2HkqTqMCsy6QOxrw1h24jMMJLDyLqYGLzTqfKkO7+31+jU9tWQL62Zudi6g3bumr///'
        '+vp+rX3UCtWAMYoGuiHN36un8MRlHUlsxNtRbGCjVoM1BkmpUQqXK8UGBKw+KYgFGZ9gQNqwzU50//NQxDEZYhaZltpK'
        '0NXGBVROdfhYqvq2omZ2bcOvqrq319PzlWRDCw9VzFaZnGUJZRX/SN/Z//2Hfr+BfqBikR61WI2E/hnRP+FER+r5EZl8'
        'nf5iYyTX7IrNWohmkDlae9If1FuFh1rMlPFCLIxwQV/M/sbrNeyANdiymyN1q6MRz//zUsRAGTvWlDTSxMi6r8G7F5kb'
        '6I1SIrdfT//////////9/rt+2vaj3ShjvLUUzYkSgH+3P5/RwwnWubqPSXDa9veM3PsRvf0xz5RcsOZFm16r/XmRkmUA'
        'g6aCgGEIkrExc8PngTFAsG0kzhhlZu6TwLvLhtiZRioO1iO/UzTtQUCB//NQxFEY4dqsyshS0jUCH///++UODp/8uFw+'
        'GNJT2Jr//UyDbI/TUtf0z9badwvUMMRaghjanX//v/JnBAAAeJztcJA5AYD4RSIIg6lsx9IYJWFzzy6z7LP81Nf661iC'
        '9indSphLDwFnUGooJirv///9lj1HK3zKy8vp3VfXpXTt6v/zUsRiGEGerADAmLQG1ZpWhGUOT331OIC0KVwT4iG9Lgug'
        'lc84HBnNXmdPuvfinDBa9sDhLyy+zh4SwPjvSNtgGhILRyyhSAQEJKjrMspW//63RTWspUmv/+7WptBMHUf////kUlh0'
        '7xX/61B2IjUm5ZmAC0tY6mxlNrsWgJn5wQjQ//NSxHcZwg7OfnsEtDIr4iYNAktHKpNh4wM0NDf7W1fNz0iSZbVqPOiy'
        'Xnj4kYDCcUfbIk1DC23ISrVFYkc3KBq3q/wyczy2Z8/5D1EjyJEiCznP/iUBRQ8XAX/////1VqvBYGZQMoBXNDn9wn04'
        'Whw1k4I+a3e2QyFlreYg8Cstv9z/81DEhhnxhqFiy8yYFIT4v2qz97L2Ntd/N8rp8Um6VNG33lVn01LHDvnlTuUSrWOX'
        'vmi1mJ36t1GfDSuR6vyzp3/T0Zqz//iWsNKIlv//+KPO1ZU+UTj24+/zIKZPXSkMVw3U9h1G+yKEhIaSdfQTqbpcFz/z'
        'VVhS5py0aftIIW5u//NSxJMYyXqtlsGFRh+9+0trTHh80UZFXNLuukpUQ38rnQ//aVPpHBCjHChp+zdW/k11u//6ACwU'
        'JLMNAKBK2/dr/qWVMZBrtkt/04QdoX2Q9g5YkWBDRxwzoai3JHRKx86FrpiLI0oL37cinPvi8aLmyOioWyFXW22jbOhJ'
        'XOouHQP/81LEpRliDsmeeYTylHOTdwIS3//vOkTakdS1OXZVchgZ/v01/rTR7Wf6S6qH7KXAAEi+0f8wGpaTHRtCklHT'
        'tOrMd9bv/5+/VzpRBeOfMGrR3fWsq4r+kco9p2yD2xmQzM75dTno0c1QfNDyWSRCAYJiZ8/Es/9n81lYwgEVw5zrE//z'
        'UMS1GHIOrZZ6SrL/6f/////13///////XzKxxzD8eoKST91E7ibGeGNQD2ow7x7gypECIh6fFXJYpzDcTyokETUrRoiY'
        '6TVkzbaB0TBQ2sdMl2lroLnl0YjEwfRchQnGydHAsNkkEj72JrtveSesf/EQopIPw+zhh//9Hwf6vyX/81LEyBmr0qVe'
        'MsXArV//I7ybpi5bdeGtgTgzDTgP9Q7+LAeOrNdMXngNVKz4rfVPv7s43nzn63+RJPaaJr2OqrVbs6CJOKKpBou63OpD'
        'IQweBhrItfv+v2uoig1Jh62YcIoZzf///T/REWibPe87oeZNC7ELK2ZA08UkHwIRPGKPHv/zUMTXGTmulCYw0pD3cl2e'
        'LjzxWtkjLIWEqSwQXc3MvymRFCcYcWpcIJIAAMw+VGwpN8wEDlLVqcZuKRy3YHiU5D0KbVp8D08ZJq1qPLJ578WFBiFM'
        'lESSkeI7ZYRMIEYneetAcIGTfk5Rlh/tjPBtlOu3Ax22mKPOKva21/NR9mf/81LE5x9jtrmOeVFeWqFR1Rf1K3//////'
        '+jbHi52dnc4os7lFxMQKFnFhBBcPvnsdBwHD7OMF31P4Dp4HvWelIAhjTIUGt/6xgpUKdX6xS3L9BgYE1HwuUGiQpzlT'
        '/ptJ6qaw68a6HbjEuy1E0yufVkw/o0vVKj1qA4ZTQnArJZwn4//zUsTfJuO+qa7KSxWx5JYkLDYhvLC2iRmbZ0pKxMLC'
        'UyqnbQUiXLwxvxR6cXfOT+i+iIuHjh/i5P9nNzJ35I1D6kZ5lFn///////6tMzDzzD7jQBg0muUZZ1qops9znUwxkach'
        'qnIQNQ8VAIkCYODxuo6LhcNDBIEQTug8MiWNEU8V//NQxLku1Ba2TsMPGI2GFaac5E1Azzc3mv5jCYiog8jLOGgbyaYQ'
        'CwxblxyO0xMUqUJxxr/yMn/lQib+7C/1nvpd+ViUldTlQW+oleFO+YGfmd9HTUSHmUqC1YwVBmgjjqxnMmsARy3b2/9f'
        '//+xf/XtO1SqqIc6hoMUKmShDSO5a//zUsRyIbvq3lZ4jX9n8hWXI90a6fmGDi8cwix/0tl8JjirrrOVEM+2/1hzafKd'
        '4ShnnEFOoBlYys4Z7gQ8wlsSUhnxLDALDy3bB7D02/aiTkdzRGdnlPOF+hooDepgjeO+w59/N8dLeh6I5EY6mv792Iaq'
        'a7U////9Oif/9DvSe1lN//NQxGEcq5LeVsPOWl5j62vm+3q/VCzrI57UtgZ/VYKwgdnQABIJJ/T5ECEfC4FwyQOKkFyf'
        'mDEnW1lwQopYl9EwF964ofh5Z9FIaLj/ZNH5djv3PCSXc5wIe+3QBNnDFoyo+jP0UvVxRCMKMpyFN5VWqFXRDPp/////'
        '/////pqi1v/zUsRjG3tSzv55hSTKy2itI2V15Ko9KrO5JJCUlIBB+q9aIlDVwF7Ux0QD9c78wxVihZpIrSM2aCzosinP'
        'KvT5zVjQmBsxt/mWjmjRCFiZk4RuCEaJWCr1gFShH/Tt5/7wz3g4vAA0QBPcoQsCbKv////+UlnuCuepHUUV1BNBFq6g'
        '//NSxGsZGabuXsPGWp1i09uKgQKNGeEgExHXRKC4AEm0OC+XDY/KhzSPV6xdbbO9ZYclY6XnBZGgehwhHYSUbVGpGl92'
        'l8WagjaQtEiTkCYOlAkSHQ2REwkHnns/8eNs4xX///++gskNPS9z6siqpkEKzid/xoVKpypyHObCMMtVS2P/81DEfBnJ'
        'Qr1GewyaYsJ4aYEbt2jRa8ZsWaXNPOO1JmmJC5EpJQ+1xlUtTQTYaYJio1ULpat6XRHZVZnPHsxW/+7LXyJQaWirpKyf'
        '///////7ZVcjsxzMQXnMTiGD99yKSNXqawFyhbfbTrH6zKQDIeTxMheM7wcgmKw5GYXGaA6V//NSxIkae27NdnmKttm2'
        'qg/Ho833mfJJKQaREQhhB0p/JJcq/K9Gc5jr/06adWVRUXdBP/9fKr0RKtSj40YUgFFiMPOP///+qHGGoRjVflwFs+/J'
        'EMwAOmEG8yjBf5Hsf+3ERc4aNYdbBolYvaXdvaneOZakwe/HPnHv192rZOvhwA3/81DElRlCWsl2ekrSNbm5rmu9NNCG'
        'zatIEAlAyOp/LI9HK1HZa5jn////XvdJ3NOecl3////////p79eeqNj98EqspNqAk5MIJ4LEKYjLwjHjQxIULYD9DgcC'
        '3l5MSaGrX7EbpiRHjFEzGj0d0ES5ZEDpCBZao3QildhY8QMih4VE//NSxKUZG466NnsE7ILvGG2acuXR82oojlF3YSVL'
        'f//+tWcrGpwVEjOHmQ63////dYEjpWrQAW5bBjagEnNEdidKDnm0Hk/lIKJUQDAFYREz7ISWCHMjkfLfkmq1WKUUJKWA'
        'MPNarLYxbM5lTe4VyQFLfrzaPUrVEqUEOVwF/6+FUmj/81LEthnSWtI+eU0e8EzoMnSK3L0eyvv/aeYMDqnJEs81jdOA'
        'QJctkH/dIEvLJ3fTLKyQBORCB4RDig4ESFLQq1EZRoG2GJn1FOXLcj+cy5TDcuN/Jrsm7KKVxwtNdzHzfq9YJKUVUO71'
        'uC0V1VDPNKpHvbAkcxQYBHsJNOlciWWQx//zUMTEGTm2rVZ6RJqv0pfU56v92hK1SKUilb2///H9k6G6cbUu1au37I52'
        '2+mjTvlcxR1rQKkZrg9aWxNXa1MQcwwOoaG/8jWvgbB4OnDxpVXHN+6qlEpdFQPszozmJ9VT/0fpztr2oCQtut+5/kXN'
        'ezYL1u2xW5XSCUtsj+EyaoL/81LE1BoiSpjewYSaaCyhBzCSixF9bBFx0wqqkVJVpy0hUw4yu75bO+kl/RSOQDREJtAt'
        'gVStrmq9rojqoMCOyGd829Hys5EhFaKu5lhiCGIYrVu1k22fPY8+6SEtLWtj6stHt1/ZKKqVor310ZJUwe3F30nXvVma'
        'TEFNRTQuMKoXlv/zUsThGLpWxl56BNrqKt12u39puFMFRKMWz5rMMoXEzDGttVgQlRJeN4/md+E0srU183KfP2uLe2bP'
        'WJUiGBpQNmGrQGkrDgwTOUhixxN8ohmOmraLOuA9F1bb3s6me8m885lod6Ca49zkGK1YFk53Kp/9t5bKWgAhJ923bBBa'
        'SHA3//NQxPQc4zZ0HnpEfMgwkrJADrQtuH8gWsAVgnyTuY7gEo30bHhS5LaWFlfafFwOA/TshsKEy7lUqmPxUKPcRClK'
        'nkOcz7FKZoWs33rN1BWq6cTJQlDfr4nb54nVisiKBkidOq2zOS1wujZcajdD1Uahf19gVGv3+/EzelDGPeVncv/zUsTt'
        'GPEmhb9JMACVpyxzRIzgjlY0rueFGfRYtsa1SBT/x83zff/bXJ49ngQG7Kcb4k8V/v0jyVrjFY9b+24HgRImt3vu9//9'
        'f7/u0ouOqYVpWaaBHxXVP/Pe3s2wpx7UL8t5VUhUM2iJV2AFqf/BKbiSCzHl4MJ0gPCF65I9wMeI//NQxP84S9qmXY94'
        'AYcOVhMjDUFT0qiTYiHRWqdy/VpczqhwVy0//mURDu5UFkdTPZSlKVHQWEhZ+u74NQaLSI5T50BAYSuDVmVqBosoCoDp'
        'GCoaplYa8qG/r0IQAFzezQKSXetDxUiObSmPXjHCzKEgaZpli1FrYWpIpqBWTXIjpf/zUsSSGunuqx/GKAAFUyjUTVVC'
        'B0uGzozT9hTOAls23zTOx1U0AEiDJKVK7rrGE1s4lqG7S13oX/3/d73otnfWlH9fLlo31Sg9IKZUsv8lzflhShDIpf7d'
        'm7t9mIkSUSFVpgGEMlBNBAwlfjNE5pnWU8VBjA4I3p35uJxQlh+QlDF5//NSxJwbI0qKXkjFLIrbMtELlJAZ7r+d1Vcw'
        'UDMom0KAqVhl0od+HswJhjBhFPYnJipVUMskl7mbwpilcgAT5pIxUImQrrH/b90YGN3N//pXWCI6FIKIg4SkTFHG6cx8'
        'qRdIBLTh11DrGodK6MUaGocMC5oQLQgxJkI9+5bZea9vzXD/81DEpRr5/opeCkYcCnIpqAuJWxjzrD96kbB54RvcKCuh'
        'HSigv0LrG7BKRd+hSE2sf9TewwoWJF3WyxzbezOCKtKQOBYTIUi5IGNENIUqzUF7RgKDRfEQsOtcMhHkaBliqhq5FTK6'
        'wiL+95fN7mspVXKzRCLHJWt90ahzTZVT5dj2//NSxK4YWaZ1FEmGVOhaU3sYOrZcqVy18BITNgDYoV0OeMo1ANRKNOSO'
        'Zm+7Yloe7iJUPWK0QTl9I3WxLJ5feiop1fXU5bNiufSaKUZy5R7+77pxkR895OfazJ+ZK9tCCjTACBxAtlKJ4pKuQTG9'
        'rMmlrhxPfYVp6nKsKsF6K6eunq7/81DEwhhhnopeYYZUn6VVEKZTeascuu2gIC8wmQTkJDKoLYQPWgqE/ROEk9lopFZv'
        'BU4Hplmdwgdwx9JQOMYZ0cRCkPU30WBosg4Uokgh4qmRwERFziNh9UxdigcQiEHvSYMYo8ZpQnGpUnKJS65qSGOuWwUa'
        'nebWgmQq2KYqBcIc//NSxNUYmX51vgvMBJG4zLrpOtHT0vBc8wYFTD0ZELABasOhlGMTC3zC2xrNVqkgg664N0QjIyqf'
        'SHOd/pbnc18jKqbOPg5xRARoeJK1QAqgwOUKDGWCRKR75hw0RMr65DUF7miyBx82wch8USB6nKr3fqpMQU0pBfS2JI45'
        'mSM2hgH/81LE6BuJnoJeOYY8gbnilmNKf6XVR+EJJLovVVQZoSdt+pPja0fPMNQo/y2sjrDSBYVBJyMjAqXmZt6wcWZh'
        '2bQglgcH88UpfHbL5g6WB9RB7BrIhWUcXtvuXxaYRxlEZScIt4eK2lHMM2dP4vVMQU1FNC4wVVVVEMTltrtO+2szxv/z'
        'UMTvGmGafl5hhnQRNNV0JT5ta9GGpAOBqaDhyLEpyzb367xThoU+83nk7SJFH6n5LEel52GiUZBhaot8teERSkeocEAs'
        'AFxQiK3BagWAI2sVFWlRQIOMnUFL1PTctVlaAHztbqF/XY0zVKfUTEFNRTQuMKqqqqqqqqqqqqqqqqr/81LE9xtZ9nGe'
        'YYa0qqqqN0ctssd2120KqFGQFirKRxRZTX6HrTlRPVB1G2jD5naEqVldytjLNlWMXdQ7c7NVGL9RNARUkGRYyHTolCRQ'
        'GUDnOZ3Y8rALzXqtFVqsN5ZuXRwFi/3J9/tVX2e/YqpMQU1FNC4wqqqqAgJbhTMskn8UsP/zUMT1Grmmhl5hhnxdAIEK'
        'ECioiIH4L3hQa4vTmJE6XM6+XbXJNWyRXy6YpltrOyMpEhlKaGlLZzldoz7uhl50yco0B459rhK2wcZSUHiE28IhdiL4'
        'FrxZ3PNmTzFldik0rYvtvldbdxzYpVVZKkxBTQeJbpZl5AMBMH4glAxWkBv/81LE6BeRHoW+CkwUYEcxbSp4EYRpM7Ad'
        'z0m01FZNwkmlta9n1w8MxmUroHMLVuGaZnG/vNSpsgrangjB9ZUFixAOptFXBIkl4QYC4bCoQFEDDAtVQuwjRUhCWgo9'
        'DzA2esob1ta17F16+UQ9dNVMQU1FNC4wVVVVVVVaJy7/eX7a9//zUsT1GuGycb5JhpTD2LAZD4mCgaFHl6mNIpFtDBiy'
        'JpmrtFaJtDRiVWktKE4Q8b0UkpKzbOxt16Mw16eH/u7SfJVL3e7S+U9M7NCHOjPd2R+z/06troz29EdXt7XKvXx8hcWW'
        'm+RbYy9yr2oo1Fkk5NbZbbJ/GitiRDcAbGnYKQXg//NQxPwcSYZcVGGGsGnl26c29fGEBY6EUZKUVdAw4milip1mQg13'
        'MNIp5WZhRURVIdaDKnKlqEu7dH5mIrNJShFOpWJM2uiFKl7rUlkQnVFZjGbZ9C0RHPJ2RXuiF6zjk3JtkMc9NiKdiZ6v'
        'YwxdKdguVYtlAqX6vlubjZ3SYQG+Av/zUsTzGnsKfb4wRaQ73hXQWTCUAM+ITWJOKXlDuzjXEATsyCq+UWZYRIAEc0Q3'
        '45ddSUQID5AKub58bqXrEoqWWtuSDSU80BtzkswwV3bimF4HLgJMsoxWNy+ltNcmNUksvS1WiUzLls0ZWzstA0CRssx7'
        '+H/zm8ncgaUV5Nua7DjO//NSxP8dewZxv0koAMu49sy6juYY7/Pufcu5bxy7jz8u/+89d/lJS3KS9QRi9UsWe/+//9//'
        '/3X/////+////+//7r54d79/6zDvs+U2fyCVicRZLFilEnMbDUaqCOelE83JUWGprUfVICCkri9qsC8E6WlCxnYhACUu'
        'hDRe2LsZScT/81DE/zMi/n5fmcgAoXUTkkzSuKPIDabilWkOL1hnbzHCOKRqiRwGNJLnD5dnBD14KvS6olnrZgU7E4TT'
        'ZuvP26ayjnUbk1P4/v4dcsN8+8e8e8W8XdcU3TvKx3DW9fGsbvm9sxt68eFHktiOxxo81//////////////T+lP/////'
        '//NSxKcv84LON5h4Av41ePfH+Kbpr//////FInZASJk/k1gsfFGQgIgS0rhHYi8LGgqEY8MmaZfo5c9Qc+7FWRt3iQNI'
        'Uti9/fck3SkLc+5JBUhh0GTdZsFOYMYmAwoOgATyGsyQKwW0uH1JsXk0EKloD3lxEkhLRhBGymxwexCHqUH/81DEXS1D'
        'xroP2WgD9IvHXZNFEyOuqkXSIVm84Xh7GJdL6dI2Om6nWikinaiky6KKTNWiz00Vsr////9epaqN6SSyxnRsZUEWdVRk'
        'gYnkjVJBjYex/UidPajZl88outzitpGnptEk3Wg199uwuvRL5hYMKNFxzsqjdA/zJlitrjGX//NSxB0fi8rWVsGK6oYQ'
        '6yzpuRZNeVlAQV6JMabjdkzZz9jgEAbVZU/S3Ggq6iQ8aK1Z0O+kRFfcpejqVrKJB5vW92Eh5ZVKji+xkN95L7I3Tryr'
        '//+hjPqWZ3mRmTSQy91pXUtdK+UzqmJBg/UqjBDckSTkscmrJm1zmJ4GVFpBrg7/81LEFB7DsspeekTSmzqidbSqTyFe'
        'lUIgEhTGk1hS0rdUIJM1l8QtotayR3P/9LNMKHA3ACBQ8pyzGqlmojRZ91PfqcKzNQuyEZbo7XCgzE3sS55/V0zpdP/3'
        '5Gfs7H7fS9jvIjPn7LozzvohDo2CYRoMmw1V50AjbKwY7dBX/4Z/v//zUMQPHDPWyAwQFt1////H+ypt/7338utA5XXz'
        'V3DE3xVP/foDsIckExBEPYhDoOWCQAQY585BBgGFJPQobw9k8d5kgOwmZoVvG8fCsnuOG6DDQvKye4mMm8/A7GVCp+Z2'
        'KjvXpM3OM8QI4jH59v/gy//R////9c//9dezianmpq3/81LEEx40FtACEBbcRlviXcJ0ctsn6tbY+lWvkoJhEecJ49Gp'
        'sbkkNwVPCUgSkhGj2A4GI8jgdmeGBqSwHjVScCGP7kh5L3qk9A2EQ1YalQ/GhIHZBKJNmZ4mPHhQP430iWHEVUjktfT2'
        'U9/R+q3n7e1WiHiHeJh/9pgTu/xKQRFD6P/zUMQQGfOnBxxgxPrOlx28PZZiVWeXNfzX0alFqCPaFZSGLyV6HyEY6M69'
        'mXcXmUfXT3L/pw7yRjnZ7r0odKnv/9/XZv///p/ndGddEo6PZ63fZVyU026pVn/6YsLAqPGo0DJC/32iIl9rBACu2nMc'
        'OGtYxwFX8cgRbdt2LK9TZ1X/81LEHRjbJvZ8MUc+EH+0WcykMp56oavmNRFd1XvOaRf/rRV///19rKdC3Vzs6IwVd9tk'
        'vN0bRtbeiZK8vaRspOOzFoucxJPItTISJUeKroFzklVoaIeJiY+saBLwijU5j6iQVYDxPnU8lJpbuKyIykB0NBe7otaj'
        'mjWZdrc1qXQIqf/zUsQvF+na/xwKRBpnJ5L+9BDN1OO4ABDAxYGlxufILFWXzVGR/sskKdo0kgtlWscpKF9muHIPi7Tz'
        'gny6333iJmNYyqWeb0YIQuVJFFMRWeLPBe2jYOPPprftJRyKFNN3Bc2tGl/9TcqOVnKxSidHVjVKwZ1Kb9DFb/+Uupat'
        '0N+Z//NQxEUYk6rufDBFQr//7/5WbqUtm6ty/+hjGMUvb1/L5jGFKHR7tvtkapbrWeIbNJQN/TTp5q4Ktgtyd/J3k5Ry'
        'MQWTnDDw/1EqDvZk4j3y04D7KZ5lEIQf6Ujl8SirLYkT7IIY6slTDSXV4cWACGkGl/YhlvF5QQAgoMJIPUCK0v/zUsRX'
        'GZEa2nxLxO6Ex///7Pf/0eMWv8c7tIpqCHhWiIh6QTD+KjvRJIyxji6UnqNMy/v5xfGWBDfPyXCGBME4tlJ+eSqopxDe'
        'iO7u9Lb7t6pdFyvyPo/dCbuslsxbZlspHc+39NXO10P/uXGOFizD1EJOkUDbGziljgjaENo1deiy//NSxGYY2s7PGhsL'
        'CGSw1agVyh4FzZAYEA43i8mL2MmL3wuc9qG1DtqlxUC/exInE5SwKzFKV/1q8Zjz5/2OS0gpEdK1Oyyr2Lz/fs27IZXq'
        '2yOWVv9Oj//5mCsYEcSIiRd6iVYwO2YTyWR//sV3hqu3gQQhGFb6eUjIjFC8YZAIAC7/81DEeBiiusZUSMVMikraBR2c'
        'rOJs4+BzPMgspNBgZ9Xn+AAiVLXSVULYKwvtelUFLsWqtb5qCKJDi5c0GBgjOhsA4NsNKoHI5ZNGjlsLRtr1miFQg3f/'
        '+//////9t6oOPTWwFJygCf//621m4XeVx2piuLZdbewu0I8ybK5mimyX//NSxIoZyRLLDOZSjA/8onZ/NlAiOqW9UM+M'
        'CL8wZVDg4FZMQbib+c18YHUEagHd8TS8/zpyBwQcuZSG7pp5NBJhv////////ym3J6KAtJiGOpCMSzOL/J6hztzP8jkC'
        'HCUfYbyfKiDrClLlDx/Qan76bt+0nD/2hzbmlMsw3LBSz97/81DEmBg6EvZewU0adGHVWrkfEUk/HPm+pb5dXQwKl3q5'
        'bWUHy3UYbsT////69GQF0E8gQQijRt3bd1aEICXa2QBAmqzdi+IaGnJ1IA1w+h+kD4BpHOOykEW6a6En7dWeW2dcasvb'
        'T3XuX/Sd16IJIwTZogIg4P4yC6+C0/Y6v8m///NSxKwZegbjHnpO8KJInqVGV8M/8SndIWQPODor///+/cuaafJiMyGR'
        'UKCz3uO7vVqqoKT9set322yYRBM6yNEJlrWErVSD5OEkp9sBPu8dnYqyug9S7DGqRQa2TRUcqdRICbzP1blKXmemrDuk'
        'GJZDQxjcKJUXQ5RNXhv/vrT/oub/81LEvBrR/sr2gtCc+3/17X1oaiWylaxStQxssMYwVsyxaoVXJCjTst/k8FcoRGjw'
        'FMLcUs0Oih4aH0esgetFXVTBuc1k0Tps+Yn1HLFzCDubapjZozGZad5rH/t9U31z72LLRNiCEDCu2a1cTNeucdYdInjv'
        '7he7q//InYaEvMj1gv/zUMTGGWNi2lY7xE4uWhSR6bo4d7Pv3w4gA1/wk2rUS23cE+IqhOJ1yvJqA7aBy06aPU2oeq/Z'
        'NXd/3NU9rR2HNJxaC7SySBPUHNXhsukQr5HvP9d/md8z7JFIzlt1XSQoGB4UWCv6kG0qahimwC22TtISYouUFUfsrZbo'
        'pRIkFKn/81LE1Rq54q22elCSoN//5nDodQEgDQk6C4mIZpdn4hCWWPDt2MMTte///moZFTsRLSjU6lq2LhGUnKay0SW7'
        'LF95yKbXb29asUwoqkQejpq3iG/NkgmaJ26XmyaSCpldxAwWEhgoxxBpkgliSVqy/mKHiiFVMTaBnBRKj70pBxYdTf/z'
        'UMTgGXG6kHYDzBAAY//t/LrjgweM4NjgGk51TAhMpeqgDghEEHA7oCACBgEwBDFeVlyykIgjfRBo9qgwZH8hr0uuUXCY'
        'UwU1vTcUECAj+nn86UPs0DbdgoUBB14/Qsm04DDBwbFDwoppYNuQ4mNRdiYDqpWKkiQRmiiE1ejO7df/81LE7x2CGpJW'
        'YYS8rbtrbAE1aKk32//VdswEwXrGJICSNSAJQmRDI1PNE1G0g3JqXXsQUoAgxLJNL7Q8a42fnhZXNNByoGcgLsamFZ6G'
        'y3M74zylBC/3mrb2kdKQ94QYMMjoRF2S5q1uizL1nOWf+K+qlAmu368enoIrWppALOcDEf/zUsTvHwGqjl7bBojmVQw1'
        'GnCm5ZJhbgxIRLMBYSiKFDW/hERvJoAo6FNLpUxbtWTw8jPVoMKReuM9kNHXkHo7EfHi5poerL9Oru2K4mE0/0fX3cqq'
        't1HnGDprP9Gs61R2TVU/TZm0snovs5P39/b/TbZDV/bRl9/+/RFWwuUHglFv//NQxOkdEbaVvtMErGIAgcy75rb/b81d'
        'lBLaTEnKdZIEaOVKa0URHSEQnM90Rs+2iNaeKzMMdSmaufw0WYtZVnV4YektioWuyUUXwZdSi7z2a2ruhaHdmV0UUxiH'
        'YHhH1D1RWfdk/37J12r2rVja3/79fX7+S9f/2/v2UjWr43q2w//zUsTpHSvCob4WSh56qgCB3JJAG7W59yszgwdoTGOU'
        'xBUwZrGhrQ480goGlQU1hTGWLC48oIzCeeaEjaQJRF7zqid5q3atUVfT9E8OAFA8oHy3oXBtK/fw1cnDQQt41AZBDDgs'
        'XcTcTBlV4r4DuKXZcBeAGaDUB+EEMhQODGaCoiah//NQxOodU+6WXtMEsLPuBEfq93i+IkNn1Sm6TYxMsfslFrOK+3zk'
        'MQff9BQbCKC//oB+BHKOScvVADjbeFoKTVWVNlMmtCGsHvxNldhiuqw4Ib2C4dja9oxTVJRDPO28Tf4p/93z/fWfSLv/'
        'UfX+d/XtHwzsZxP0WoxHyRKJDFwcCf/zUsTpJ8oeil7SHvB10dhkJeC7Q8zDBLCsFkS00lC1kKFJSSgqAPBnpdHk/H8r'
        'UNXaqPGWuWNQq17BgMr2Jik6jDIhRdk///////p4/cbqTvRFGHUwgOAhmEwsDB8osB2GHCQ0ekcH3OJiDHiAmpVAYUZ4'
        '56xRND8Q0KJ5LYgTrbwl//NSxL8tvAaRttPK/ACYrNeVRGGLK3JuVsfsROPMMVbzKnd6XdqXg9NeRZ5etqfqoc7f//d/'
        'gUHWMBwFghigjBc40kl0O++V+/vmero2YQSDxlmjiWiP//7y3pYHsNt/9/0fWbWDjwRQgOwRrF1Vk2mVF+mmTA4gFMoc'
        'UQqid2Zws63/81DEfh3h/rW2FlAav/rrKM962sy1Jb2LR1RcaXhI4Ia/GctQFAU9cZhAmehm+4lEMjmbwdj/y9pZCTBW'
        'DOBDAuM7pDYDlrMBOZUFwyAMpilKzobXzPUZJwQo0WZXCBRK6/+xRlIQ0p7p/9P9f9v///zaIbl6tW+z1Tr12p+nXdDV'
        '//NSxHsf69q1tsME7obKw7EtggNdYB3tHnLKh5owDJ7zPATcSjcaHyUaGj/l0vUlEcKR06laWrnpLFI8cXwruQWsjEAO'
        'IOAJTGmuGCTDxBy0djGLxpMhgich9HSECte6XL1wtRxeZWOnNsW490eosGDnCEMmqxGcRMbrWa2auUHElCf/81LEcSRa'
        'CpG20w9EVRVJCmiWa4q1nRFP9mK1h0SoWOeehZhM7MffOuJJI01q0yjkITd2En45ykWBe3dRnWGabMRgrDnyZfiI2o2p'
        'VyxtbdPZsNV3QRNRJRWiko4g4Jr3MGqwd/I3WlQM6PYTFOnK0yjruu43xJqwPBqPn9u6b92qof/zUMRVHun2vb7BUUq7'
        'q26Y8kk4Qkj3HFOeyQobcipNP//vJkRKVUFQCIYVcza2WR+lKV2QF4C25bJN02OwGbPKizoWdNYOIIpzaiRn1b3x1UMC'
        'kaGmLiLCoKpWXfVMffl3Xe9a6KnEmNSk4idiOyFf199a0mcVAZn0XyH29PbO5FP/81LEThlCBrGeewqymO5lH0n4Y+n8'
        '1Qz9riev7hieNlv//SgP+liEbgNZm0pVtfyxnLU0mTRYgG3SQilOdPjOvkZayJXinUjs3hXiIwMH8Zm/Em27t+7u15+2'
        '6h/Oftuv689hU9zLhMgYhFGgggQIGFId5AYphBn6CFrlDAXF2ECDIP/zUMRfLcv+jAwWEg3CmLtBtJiJGKyNvUaNHq7c'
        '5whCCiBAmjbhk0e/+TaSqOUXoCReenDEILztIUMBR2eocgVb9MROmmFyf/1ekBIvSBBW4gQMTqEPPYVBBi5JFfaxJjLm'
        'kD9LKhI1nweNuwGjjJyJ+v/+edrfses8M0FTSTdf3///81LEHCB8FpgAAZAAxrUHLdKsUXELUz5TSbrWg+ug5scdubZp'
        'VpUsu2K0s2NXur2j5GJ+bdax6cTj3nn57/eKuRi3Wm0a+rrciFe8vdHKOrFauMUN8tTX7nropPKqqe4FqKJsdTOSSbJE'
        'HQilia7lD6H3Hdk1sdjR4sCrtZdUnBWOVf/zUsQQGXjWploCTAwNDno/M+VjFzOsk6WyzMS1/WooE0YB88LqAzBZwLUJ'
        'MtWGjDj4qQcWGDqUoF0HTwiOxI/jn2BXo2sw0VzbDjJGVrBxp4iVVKPJ069A6siI3krjsNNSKB9nfvnYkmA/PCamMs+b'
        'sSPMZsO0h3DLZdDFzMYjdWR5//NQxCAZo76uXUsQAEW7zUc/tKxEVCnDiECEU5znEMS7Oz+einIx6MtatNRkt/zkkZCd'
        'Eu+p3tu/Xp6U/T8/+irvu363VP1snRnVfvILEztklDD6g81/7WtAAzn4lPSA+gRh+F7kVUOQ/C8HuFJxBjsWOvqIuW+5'
        'rtpPDO8pN0zenv/zUsQuJZOmpZGPWADy43RZJrEd2rTX1O6c8y57Qt3T9F6Joxj6UaQaT4f+0eVLnRN7bq3asPhp1v9O'
        'hstj//ztXUNa2eGW1zGsUXtrIieeuatn3//fzy2ItVjM1Nzz03xNM63S7bezVnuauEg5DR9SYlZVh2pJBT7/FBCCDDDk'
        'wwVV//NQxA0dSbLNlY9gAEuZCxN10GgpRGxrl4fjHRaFBuZ0ouxPyE5NHV/e5l19Gsm2zsobeJFD/atO2ZghcSYcVht2'
        'm7DNI8xUmkygdg/nMWMRT/TNETFbz0OQ3Whs7LlEdaXOrEYALJ/0l/1iD/D/TdpUZ/7EVYVDZYu7ecf/vGygRf/zUsQM'
        'HTmq1w3YaABOLtLICUrKpdm/pAMeJzGjbipZbxzTaUbcUdxLDUCnjAlFzMdxoZFBZQdS45B5G2v02RzjreZFmpBLmC0W'
        'rRXrSfWkk+a9M0NkpgCshXk6gKdC3///+5qi7HECiXNDEcfitZ6ndRn6dtTukuGmXgBLDm3mFoTs//NSxA0Z2g7SfnoK'
        'zNrC7aAcb2nyd5i6y/FNeVVAwJ9xgFBE3liLcOn8OaxiTPqrVTq4dFaCgaWohyTdTPWZ9ytRxUuQW5PX1TV11cOuR///'
        '+czryzWocbA0G75Fq2TszUee9d8WfRWEIqS2S8829XgbDFvE6cE3PNYgLtSmjaRfonX/81DEGxnTrspWeYrOYScpM11i'
        'jPdZOeb7HUkWBJdFurF01KxVQPB5VAEVN79HRHZTGFlZRWVpYkLatrv9Hsrmf6N/MX/+v9P//9DZZjGNM7ob/5S//2oY'
        'WZVkkVyaRty+3fEGEJBG9F4NB381UFwcAkXUmzYrtd0TH/NR2UVc8ier//NSxCgYmQ7OXnsEdp+zrcylw3dVaEEh1AVG'
        'AoATrnEHDEoWOEQKhqCg4BFnOa9VJ0YHfdMJ3prtd/qfLY//xL71Hjs9vkHKSBUussSkv239uBGMS9WMY777GnEJrtrB'
        'Ani7mRotL+rcuC8zQ2w6XLgn4r8NVz/7xfuXDPK2+Vpl0+j/81DEOxlxssZeeM0WMjpL8Y+GavpJvxpxlnLIp/9zm2uY'
        '9yUsv6lJexGqRUef/ro6j5slBhR6WgiFJrLG3N9h4K6SqaiiedqQC4JQo0cOAK+0egGccQag9Uu1otPJol6iqr36gbVc'
        'QQfjiHGBnCRhyLCICHu+6ENnh2QCAkc8DgN5//NSxEoZgP7SXmvMXjLpW/+3PQIcZC//4qn1kF/8mcXnN6ElHBjDBeul'
        'iApAGP/G6q7lyYKpGDYXRCEPU5ll42/UG7G27p9c3E4CnMbsNyblaUNrOumtNNke4pSgHLlo0L9gHI0CJcnNnoMubJ+P'
        'n/mvdl5CO5qLYOHlNtWPJAIIBRD/81LEWhnRXrBewkdCGiIiopjv/////zCpWipiBkE3NvtsjPKxc2XCEoSdRumIuYUy'
        'VhscVquU4ZMD1Vzb1cwXMFbU0lGjYRTCSFUpq0Zomb5r/VY1Wme2mg+YXaT5UsqprjboxS3uRs+gvSilj/qLUf61uhpD'
        'KIq1rKP/M9EqUMu////zUMRoGHleyZ4L0Bb/2dcpVJvm6RUE3UKheo84DlXK7I6vDWoXW++7USSlEZKM5ro5RI5m/UGg'
        'a+RHqsolcsBVHTAjU+/1CN7u8u3ql+9kd6b6jRHbkraUpT1IsrNoSXqQ8k5ZA9K39GTJI9LFgAZAy7bbaeXwuhzAobaI'
        '6YfD8on/81LEexmiPsmeekSuXPC8nlXUE83uyrikFpDKKam7EHHTf/82MuN6lNVLQ4x7UbOGO4IBMLBMCB8UNrelIkSU'
        'MuhlAiVkA9FYswaYi1OLHCW9JEWvfSvKtdRhirZwPr6fWoiAVGUttv/tbAosBEZIqD2DIEQbDmOTgotDhOGj7p4ckP/z'
        'UsSKGiluuZ5hhpLrUpB5MHCMWidm2IJF1fc50KtG9v9zSrPjGe7+TlaAJ1llymWvDTyWz3NGqwyVnARZHZTUlI5hq5yC'
        'a6IbqketXeIXbfLIQAEiQBdlttH6S8FQoYmUOZKIqDpSiutBYkJXaskxuakYEaziHBa1HCIHgsAUI++z//NQxJcZwrK+'
        'XkBHrrbd7KR2D0ORBIl5lnRyI9nZKULzV997F5E3RPqmyHM6qHcV0oWkoxLBbOK32WwKVFe9UmJhnXXiuWNO7b/bf3ia'
        '6S3gGMkWXGTx9wrZxa2GUTCjuw3SMOBmOLCMhlEQ6K1ZOJDEmJ9BZUYfM7Pqh0ZZpXv5Cf/zUsSlGZpOol54xM6quzsj'
        'vdOm62Zo6w4yaATamoSG1qFFDhiW0bUPPqUpO3uJ0Kt4t7HfapQBtzYfQaeggYeYUeZRCir0o5SXmKX5VLRbiSF9bkQR'
        'LpMEyONNi8s1SIuThAyPMhyigdJ8eS+UVDwThoTaLqMTY2NXHWZD0YlBbmSl//NQxLQZ+hK1v0koAmyR40Wbk+O4SgIX'
        'DIoYyA8QA1F29nMECondk3AVgLhwxaIHGYHIMRzBnnX/oK2PUK009BxAAgZmI4FgFAEEFkDSJAnyDkx/////ni0MuO8g'
        '455sSZFESbMioMwOsrf//////ixlxi4QAnC4Zm7GYfIYQnoByf/zUsTBL6PugPWPkAEgAADpuT81ETQZ4TL/////////'
        '/////////////////////f/p9fGavNv8wIqIEkRqrP9uPNgiLN2NXd0n0/G3Ab1Gn0LiKyHettbznbx5A1E8ZSPJaSxo'
        'sZki3vDgUiTv3CJCiN88FvZ2tbb1X47yBFowTM91//NSxHgvDA7aV8F4A33Y4zVVju/kiU5kRm50nT2QCfnVicMQ00Pb'
        'GFRnOyNCrgRG3EFXsbYoIESGiDkVp0TKRQZY1ez2kgRKeJExNe2ryROB1b9tmh3faERW5IFKgwIUgiSaDoLDVA2s8bWf'
        'grMzEsShCLnmmqVE59iz7OKbmU2tj4j/81DEMSRrttZ6W8vi54qdqNP+/l21zZz/9e3/7dbammOv+LiH3y6Zk807tCN5'
        'TIeMQv6KKQ52eOyNjAyaYIdKyu9jtY5tlIg51KJua49wYhbvK5p9tGO5JD7pPdZ579kVCK7JS8UG4sWUjfQzQr/9neHb'
        '5sBz0mRDZUsRErBEmMry//NSxBQeW67eeklHOmJEzUqV6UsWL2gh8qtpO2ujJUw5OKv77Jqy//rnoyGoqXHlHf/6077q'
        'lRIWDwDBrlF3DhiDXTJO7GuvsWaA7kRny8mkdlUhXuR5MIl+a7KNDSsDZyN29F0Q1vmRHIogVFQBex9tdbttt///UM82'
        'EckKbSTgrMn/81DEEBuzXtpYSJD+/lNSRXVyQT44UHPsrmO7Tu4U6nHY7Mnf2JBFRP+yzk//ZLf9f7pH/fXYxSyDQ3dB'
        'YNCloIQdGmrw+9mdr0nKTPWlJTVTfSRxvaVVT032N//mo65lLHQbWD7LXpRfX7W7X5oh2/CGeD2fjeKyNCoPKa0hbXm0'
        '//NSxBYXOkLaeEiNGkq6O2dRRbjhzIqotXXPUQEH2X2Xulv////Lb////3+f+cqEEzT0UxOrVSAhtcZXrNCZ6VtNFqxo'
        'SQVM37WHdDWsNsdo5HsSt1/d4h/80euCGcFQwG7ucIYDwRBeMZwqPUXMLp1OKHnqSUsE5dRVO8R2vjO+iOb/81LELxgC'
        'KtZ6QFFuQLr8/Jm3/n2YQ57ciYSOeH//RO8gJRYO5JVENO9u9T5b7GtWIWDEGN9NJXZZ4aoplrrrXZ4j/RDWouOoS5lY'
        '72KJLNmQsgWXBWPJqLIe3Md1Pk756Fmhq2NWwXFnivdQVdYPscNbNAEcTWwsLAMEwETJHnBq6v/zUMRFGQi+1nwKTArv'
        '9T/TG14+wSkgGdEtQoR6lxK4NeLPhsArIPO2rcoK1VE5I7bdSH/2PpIkNwPdgMF1ZPWe628Xh4pMW3cVRbIOdWZioKBO'
        '6a2s4C4c6skQrUrPd0sf/L/s5UDGv6o6nGSk1TA2ttUdRwiBU7FGmLEIMSJXPPf/81LEVRlKFq5aSI0aU0AajLHjyZH/'
        'y3vS9R7+1apf92SWxkav6yEsHn4oEmg81qVTeissRJSN10Vx6at0NZJF8SrCCh9LI+vM5Al0voxd0/u+xWt4WTfluRaq'
        '6hAjEDOUpwbMiOZ6G2arL4NTOrf1UzU6Fajq0EZgUbomPq7CD0aUGv/zUsRlGeLyobxIxPIc/rpqtNySRgb/7NOMCiYE'
        'bhQouyVvhd9Mr9nqZYRTgbLOQztKUrqdEch7krzPdXjXZjGvVva+q5kb+b6lZejlQc4x82DRsGum+gFVfLFdjWiJR7iJ'
        'Tytg4FXRKT1u6zqJIBJ52moBnmImZb8usKUn1W5YQ4A3//NQxHMYkf6ZvUYQAl0ooIKgqgzUgnXQtbpP6cqJ1gLdr7Uc'
        'dbxthQ7bnE1EnnzQ/q7iRq6lxnGoUPcHXj9wjKeTUOkWK5/MGLBiwtYznP3AkYYk0R2wP1NIflr7etVbXfR/08XcCCOh'
        'Rj8UMf7hqxvay9hBQXwMUBhcH2v1NFYn5//zUsSFKkK+ZZGPeADx8iap5vcYOs4tvP1nWsU//vjX3vxsGWzvEXktCinu'
        'bCStjuiAUBAMCgQCAUCAICgYAtHZV4r9nt/7P/F/+q23//2L///6op9i6kxBTUU0LjCqqqqqqqqqqqqqqqqqqqqqqqqq'
        'qqqqqqqqqqqqqqqqqqqqqqqq//NQxFIJUAbuX4EUAqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq'
        'qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq'
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
        '//NQxAANoDZofhDSIIyq3LdtvrCACIDBBi1wfB+lcmT1voLg+7lz6z+cwTD/dU5f5d/5z+f/n/L+Q9b//nPD//7tfpUA'
        'NT223b/b/ER++bSRgLZexJzrY7PCxBBbF1ke3KLOJHTKUFViERf0+QGYFAgkGBETEgGRA9k4f2w6UHNCJv/zUsQ+GcDW'
        'gb55hnCGsIooz7JxiROROPUXvCKzgkD7XiCSTnGsos96OX8qrvTKVEJdppDiiCCVHLbE3LbLvW7gwR/IVAUqL2U8SsxN'
        'ocBP3PgrH1yfcMPcREpBPxwN2MSJpVSPhIx//95Z/wKGU8EVCdeQQQjvaHMBFcgLC1LIIk9G//NSxE0bIaaeXsIMvifi'
        '4shJOXbY2xcPXi6UreKCtrtAQs7GUdX/6Oomc06lAAef3u3v/2//lOgoaJL/15WVQ0d20tlM5nbsZzeef0sx3LnbH4c1'
        'rVbtW3/8uYfrW+/3mrHf13L5h9UAcJp07SVwDBFI01tlLNYMnmiL5XHM22Yrhf7/81DEVi4r7pZewVPtpqaI2rMslM3Q'
        'UEqYSIhI0SaUM5Y/Fo77zPxY1zt7e+57z/AYGZ0YpzBy73rWlNtC//36f9qTBxkq5NGJnciMogyK4hGCIHPiAPRnOc8T'
        'd9CIEFyhGxgxBMwFGV2+RtOjgbKyonyZBDNCyMeiGlkJJAucHgtm//NSxBIcg+aQAKMLaeGqRpoOnX/////t8tncZgAQ'
        'RBEJAHwORXqfmEWUXRXbOn6dtWF5+yYrFp2bKywVzwFHOU5nIn3+qXf3///////+iu9yNmZX/9EFMpdfu9yVO7791Zrq'
        'PqcUdhoup3FfD0IGr/tCM8b/1sSEOApTOeLgDXJOxYb/81LEFh8MBrpWekSdYAQEOqEupm5Laq5KZ///WUgh4v8M+Lih'
        'AoyjRrkQ24XE5dhuQIEBFdrGvZP3sjomUwhae//RXtfVP//a3//ciL+5TvQh3wopjMS1VRtaDLnSD3RX/tRrPWytPQrM'
        'c5TEIRXRAhbZ1cZPId4eKOUSOzle/bYUu//zUMQPHYMO9n7DxJq9rgoEKgBZUs3+7eoBjJKMeyj+qZXR/qO1ZztTcVkT'
        'J1kLLeQtmbCrHAHAEgzGUFMVVSttjmI+Zj1VyLeRX//ZlREuQ9D3zUatlcpP////////5icynezERVD4kdBjLUf/bnVF'
        'HxNowCMiZl2apQov/L9NlHj/81LEDh2hptJ+wYdAdvWEEpagYjyZ/jSoE7N/XYy+liMS7OG1JF4Hyu0kUAI0F11ug0dE'
        'xTeKTKPS/mkhJs+r3H//KsNHcW2ckO9kX/z85qljghQOCQswol44wPd////6TlgYrNqFiCSB5DXV+U3dWDLgfZkl4ABW'
        'SPqYLYq5fkz04P/zUMQNG5PuwlTBhQypzufZ1xg8l3X2LyOEm7Zn2QL6fLmFl4E96SHeyIhUtTmz+1mlZ/rJNjPjJ3NL'
        'RAhD72/P6P5inqUBJfpf/o5G/////////8r9FPWpTMxoI7EeqpL/12f0/X6ATrxD4RDilWgAAG79ZAuAlRfdjzA3tAqN'
        'Fz//81LEEx377r7+ycUsVpBsbl7jn19gKLRZ/qqVT1L7FBBrtQ8/FSzuxDK61IkVeISpJ7qD8Ws6KRHWe8RUOsgLBW5P'
        'Ym3v+X7CtcCd+pvObYxQl31r+n//////+j/N1g2KS0aIbVD23NX/3bsnpB/ie1TNAKS2SVyhyOF3DNBliLM9P//zUsQR'
        'HJPq6l56BS5vCToH3pDAEAN537Jw5AlAxkyhCNMsKuFW+0PIOUrLwKChMeiL+lSzbuhTNZYuEwWFtzxk/9LHypQhQwrk'
        'Vmlf7y1aUMrV/////////7/foReWys8bf6aX9/r/9RyeGTWGKoAAIqRavBT5/f2kumbMZ2XTMGtQ//NQxBQaCXLCPsoF'
        'CFYjSZzYXBW/SWJW+7N2u0tqgUoXa5Uvl6grD5n6UZFXlnWpZ5A09klFbyobZG2b0pIS5VCgo8jkQ6CqkuANgIAZf///'
        '/4dqXgrU+KIW3//W6DTpZ9WFgiCVI7+2Ne/yLaH+oTn0RsMYbqDrpWHUdKocEyMC0v/zUsQgGdoSzj55itYhgMklJ+uS'
        'JIIXX+W9b2sjObldustj6bOWWizkVm7ohptKFUun9DXys9DO0zDnAyGLbYcYgR1XfQjbD3/4hjSzwaHAYizeWerYAG5J'
        'd/aP8eAJ4PUvwYQwADUeDM9Q0wynBzE2TpOLYCHJNFpnV6QtRedaULrY//NQxC4X+erFnnmEmqKOMhT7go9UM3Sb3s8I'
        'YnhfZ3aiI2mbqolFiNuGiM/W8xehLpx1P/tgJ5GGoNJyMO8nhgpZp23//75t5CBnQLMu6IUOgW8GwI+sEyN3sUm8yQuP'
        'BRn9pSLds76yvv9Fs6mavWRSJzyK8Wn9zVrmar3TQ5GRwP/zUsRDGfHmyj56Sp7Nt9kbHJdh7EX4wpc11Ed7/UR7o9/e'
        'Q3kELQfLkMriI5bFKv+phAARmAw59/O+IhCfdWrtxTBUQ6PCO4ZyeMevG0t582ztOFQsWXyRJQhDlLlqO884l2owxc0L'
        'jxnydR+v6AODpeIBxj4g3UXTdCUkEwDF1T/+//NSxFEZWeKlXtPKmL5xMPuyChw+PCK5nZ/////3V4opymAvAAMq9wYY'
        'SeH5bCUGjTfBLtEaZvhEHZvnFUBSTdGcmbt/NrKLiWxljDiR1/CXwLCFOUTSnFbWnw1xYOdZTB/sv+D0FoeZvsvkJ7Hw'
        '/PfdvmQxCuc/rnuq494cFpvrd1P/81DEYR5SDpw2Dp4Nl7nj1gFGXt9Eur2E4Etp5DN846e93/AJ6ggCwDJGfOhiIghL'
        'mxuQwAehYnQnS8jW5gbO1A6Uu6jJtRiilamapPTQS6lt6SXv7E0Ty1TxetqS1psk60KMXec/ULeNYXK5VbfCZGvRPFhO'
        'NDAqmAhbnRQKxWMB//NSxFwtO6K5jpPTyaCgZ5DkOh0nyVi5oW3uRoKiIp4zao3iseMCcmv5GeAnFAnC2ARi5gQBhjvA'
        'IDCh9h6BPSAUEj0210kxW+t6l6ogQea7cHNzhkI+e9fcvYZcGOsn9D28DPthQ/xOAS1mB8IzdX+n2/9f////////+/+j'
        'VMaprTb/81LEHR/L9sQiOk3pU5Lp9DGUp9Q3jipydoAuUMkCqIFxQEUI0FQNhgUAxoryEZnGqtyxmCqqITuIyAThx6w2'
        'PGiRpogQigSXJQ6UxHayedKcIM52u9bo9BByrmj3buydS8xBTvZ6+3wt93F079IqD0tiXdt8EBf9PQo/EhgNPEyaav/z'
        'UMQTHcwO2nxAUVVfX/cr/NTWyWMuH+XRM/5Xyf1P7/////nyqX/XBiR1BN62N6JahhP/ERuNsaW5xluVkXYojGDlPPJE'
        'fMGQexM1B4XOMsWGnHt056JcPe2kEK7Ir3Ki4uWUOKGnqfaXeKSkP6HV1fPZniGbfRwKYX5JoNzySiz/81LEEBmrIvZ8'
        'QEV2Owq10UYIJHbiGaVcox11/r40riBp1HO8/3f5yY4XQkjBETIA//0Uv/55/4yWEwIKTIMasuefXywQX7O03PVGPBu5'
        'yImyjHDqpo+thd7BgSG7K2lLD6zSylk3+u2rjkf/AVnyRTjs0lXw5MOLtoHI49aUALFNQ//zUMQfGSLi8lpIxPqOBYdo'
        'ho4GEenaV+XhoTygss6kUxaQn7LDymrO2j/RVRM/Zf/7r9np/+rUVURUVjPt+6zIOZUJj1weKuKyfyP87PJW6r7adWeY'
        'eahvtHgGGv1Bqzx4hLZOGTCZhqSVnZ5CwdKkmyFRlEwBFmqhAIcJBBCLARv/81LELyARUwcc3piWImQkgU2MIIBQw1cM'
        'mtp8hY4GGDJHiyijsMNAZgAAwYcXerY1hdjLIIltyxMUk88+0W26fymfSe6OvxynVOkAPPSB+yT1vDC5yDjkEChRH7v6'
        'KqpK2aGKkOf3bc3VjN6cEIlvWsvwjeQHBwaZISkyZtKc16ZYQf/zUsQkGQlS0nDWEMgwoynNZVKmJqClBgacGiSdECzD'
        'FTZtWwL8VtZspEFwNxKY+pdT3HPfxHP/MfylK5ToGYGiZarjiVoQAgMtH/bJ1aURACDsBTsmmy1aJrjw0PZv4xosu6hz'
        'hzIUdB6n4zbUinJFAAsbBpIjW66ok522lGZUOT9X//NQxDUYiULa3nmE6C2Mk39wTi5VQGZcBw7Aowt/AiEy9ShR147x'
        'EV9Po5Hr/FkpECu5nE/0pQOpiiqGMyApO+yW67KWJJQer2A8vBaMrgloWCEloXJoXpoSnhweZPHj0aJYwBbqiIpv7bGf'
        '7IZx5nZ1K2rWEB97rRkr3b6KWt6TI//zUsRHGVtjBv5hijo6lepf/RFr+/1X//9q/rWjfvqatFGGlPrq/0VREoS1zIAA'
        'TlqclkzMwaHeIERyepaYQmGgNBVUUjuFCZZMlIjIq2uAo5G5EYrExUKFkUr/LRqVX/0RckjgzmZh1V2r/aLdRYDB3PFj'
        'wKlqkdB0REz1NlqpXZkr//NQxFcZwaLeXklNEr76sS3sQSuYyW4SsYJe9Q2IgABSbNy7b9NAVOsrIxNq61pHQaGhNWE5'
        'KMWx4PGxVAJqlF5GLkYyDjWHkSVL3RZYNP+5mKUK1DrUuiPmY9EdXN//9H0y+VWcMWY2n//t/e6S8yaN+Vvd4oxSzGM8'
        'EdBIOs+NX//zUsRlGcNi1l5JhK6pqoQADJtHt9x+t2FYmj6FeDROKQZMEUxSW6JQNRn57MOQUUkWSjmnY8sMcQjW6b50'
        'VBT12qceK3+fMqs85FCA8flK5Wc83yjtq6e1M6oIqLNL7+RFuxqG6e6//6dNpXUzVZtOivSqxjyKwACljckkv8izK4VZ'
        '//NSxHQZ64rFvkmKskLxCGSIyQkgfQgKEkSKNHEPmFOjHuu5FyrLr4dRcsrwdvll7NLHvc3ZWu8ZhkVHcWxOr+r9qf//'
        'VBAw5UcDHQQodg+XB97TjZEpA4fUcvGyBMUq7O54YDZL7d0WtJx7f/e27f8kdoKJP7Lc6j8iYPd6+lGNBm//81DEghm6'
        'MqkeSYR6TNCTLbsmCQOUpSM2EworLfIsyNxyyLNR8h1yjIqlkf+Sv1jgv53K0RjIkBPzpUzS32Slu591u8SdDxBt4fkD'
        'U1jwwH0//+kWVKS7bC62Xfx9iImSpxSCsBCsmFSmIpGjSHDhTcvrG+T4f///6/7728h4ra7+//NSxJAYg1LWXjBHPjvK'
        'apR5PE975tAlVkFR6bNX28QtgXbEfilQ9+5v4DAnDQOiWBe8NRv1OwFAJghqlf5fRY+b3urJGU00QdBdzzJ2o59pxwgZ'
        'Z4MbTY68aJVCGA0G9D4+pGBgN9XMjpdJQ/0LqiDIU6jfqDwI6HudHjxgcWePM+H/81DEpC6sFtZeGF8ybDlIWqmgv5LH'
        'T+fV+/xdWaTjAyN8RRoGSATQN+dicybwRah////////5/9ZEccSPj7vmFvPrSz35YIGKQ6eb3baMs7TOyztzcupD9JEp'
        '2040unDnZkqq2tywulhzdqlaL43s5PXl5a4c3t+nl1A+iJisDql1//NSxF4vTBaldAvxyIDQODizjZ0F2URCMxeo5bkR'
        'CAYXSvvR2ZqBGVwE8bO4tp9GuX5JCMpiCoMpIrB8Ev+0N1GMRqZhllcOxt14VGK9DMwIwx7JJG26v+7z8v++Mr72vYzm'
        'tvxW1brUucssVRbrpt9hY0C7JIygxiucEGCOxtgyBJD/81LEFh3r1t5cEE3n6tXNdiLRHRWOpLHZv//6M6Kd3/a7osjO'
        'UnKoOdldnCjjGG/OcvtNOexZLJ0A5//fYKPvAMmFIplNMGxsNcJodjYqby2ne31n2f3yu+VOXvp+yQ0gTDB1glBlstmz'
        'YKDjW+of7ZniH/1lN/8EcUdAcsihMG4aHP/zUMQUHpvK5nwyCv5PvFFmTYLDQumw+SCnGJNvofYw0QAjDomhcR56npar'
        '3fjjPehCImBWr21JWreGu5WOa4Vw9Zm2aJTr//dCtdStm6OZ26GVvqVtKGe4iAorL6l/NzGMZ26Gs9H9DGMb8pS0dKlG'
        'C301bkllsbjS1vvI410y3Tz/81LEDhzpvsJaywT2x12NfX2nsZhwYY/kOmOaOoA7Qs40CCqVRQygkJDLFMyqO0TS1GSD'
        'yb2KoJr/9g7BooWOriQDR1VZtt+/XZfYi5y7FPclx21j29L9lDv2IqfvNU92QJKihAz/0KJYiXRexyk/nf9S29e1gP53'
        'KJiICZ0kpWmBY//zUsQQHNmasZDDBvAZAua0eD3FNNRqMWWALIJmm0jjrDl323XuiGDcnpD8mExUTA7MCQ4Zl4aQIB4t'
        'EdKEY9maY3hbfacYipRYcFg8TmZgaAw8U8RqenpuWlp7xx8TDESt2/0f/t/RVqQXqYQL9a0ViQAFhkv+tmm+rDMU9Ihm'
        '03DK//NQxBIc2fq6KsMFSJAsRAE83pHlEoFrXYbfimq0LW4EtcqO5PZcgBoDXpVf25ch7JFoACoROPqvWtnPTXWjr4Ts'
        '+W95bO6PPH7V+5+D8nksQIdHQEz2K5bNL/feMkLhFpy////hktehvEZtZ+LqzaRaBF3lB+fK6UtPr6BDTHtRN//zUsQT'
        'Ghm2xjbC0MwEk3qGOpcvnO+gAaZVQ9jFsSQX8l3dkGHo20AwkqnDB18j7+1rhY8gQTbkXrnufj/ll9L2gcpsSU3Re01K'
        'EVjwCDoiKCWaf10/T/+u+5ShcgsVeQPx1elFBtsrspRZGnLYcomMWc3DDKWFENkcS3F53LUfHYXv//NQxCAZUf69dgvE'
        'HM2rVhJXQGJ3HEkMYKJ5n/medBQ5xbVZ9aG6GtK3KyQwrmft/VOokx08PA9pFoSq3O2Zz/TvYwgDIucF3m2jDxVbvq/8'
        'upWt6BfI5bpHargOnUNiHqLAr0aO5zOlnYHFOAwtUgKbEXoQru6pYsVHCJCHN3as9P/zUsQvGmmSuj4LygzctSy1Tomo'
        'rodvLUoq0YtNDUKnErKtfkBCnoZQmpNOliJN4u0sKpLk9UoUGvZE5/4BQMc0wULrD9ZM0iAIFaYXqAf9SCqpjJggFsV7'
        'Y2DTYl4/BIZrUoK1LNf82T89BqMbv1UyVxqD0q692XOy1ElKmzp/9ZG///NSxDsZ076m1HpEzPn/r217dtLUb3//7dPT'
        '7/p1Uj2Q93Zmak1qlRloinNVUTvyXRk4dTxiHctF6m12k5k1vP/0XZaNubIohSedRFMOqk0yd38wC+ipfAjsoUphUTMK'
        'VDUSRXuThmVlo8ClK0vl1b5S0M6mXlqXlo/7//MbQxr/1K3/81DESRmbvqY8eMTQ8rZv//6GN+Y3zdq9Lv3UxnKVr+7/'
        'zBgMHSwUPfI1MQbVX/bS7+jgCn0pDQZkik8mlIgJKkrpLnuvVaSbYl+KJ1ZuemdH52bt/Tmy8qgizVEIoicLnR4w6JXw'
        'UOjzZ54yOF1jJAVdey0SLFMyWe5NGFLOr+7i//NSxFcZcS6Jn0kwAFMqilQ+o8rtXFtiek2LJSS45ZJI65dbbrdJESCO'
        'uFdhuhiztxhiamb/PsSkApBxay5GzwoVKYiPjq0IYpz9YJ1HAmZloviPRS0mJYsCCtE0LkSwfhsM6jXSU0b2KR1XGV8N'
        'PuMB7G3hzj4kvvdGliemJKqGTEj/81DEZyiCVnpfmHgA9zCmnjRM31ife/PeRsSrOo1JEWLRN/21quf97ia+d/X1rFp4'
        'kTNo+Y8fWYlSN1pzs+ywvac1//+pF4+SS1SQUSUVSYQXQo37LsO+pmzouAQzIouvMJIQg9pgZQpsaooDZLcu0+fY0jos'
        'J5oA/AZaw6P1vULg//NSxDonOzak9ZhYABs0cq42JYeGUOkHx0l0mbSesg01HQDgyPnIsfRrNA6jC65yh3qGdG5v8qtH'
        'ad54XOmJCX0hLbZCcHmn5fx1Trnd839w5j6/3z7P62Ta5pM+7/iP57////n4OrmiitrhENu/HgBgnWIIJ2I//6tM7paW'
        'dLAy+pf/81LEEx8DLrp32GgABQmv6CqO9D2T4MAfqelLdMr/zQRyWI6xDIG0fiO6Ric5kbJJS9WiVje6KRIn9E1RzWpy'
        'IJQo+xEJTSP9Lu+o+62OmZ09JpuqxYjWadXoXnHU82ZGtFf////////70XW9DmDr7aP9tG/pjESc2YDISXdXmzIJ3//z'
        'UMQNHFvyylbBiwLeaj5zG/ccYQJPbz6j4Obh2w9MCWcogqtE49YWS8hOgIaTaxo7GCFK9g9oJD/6H6+K/7f1bVBeqAEK'
        'uguKYw/VNF5erdP///////1rV5qD7qESKg8VrZXjSNumNb+3ZNBV8T/xtZEF9G7HNZV/Ns6X5kUiLtn/81LEEB4aDqGO'
        'wkR21nImFRdmY0AZttYPOrZEjEKUv5ZzJ7akop3dWE5BiiBYOU7PMeUS4kgUBBP66Po9VokzrCgOUKJzfYhkMzJBo4UB'
        'kj2WUI2Fo5yWJjt93JBp7SQjYdABUZDsFWb/qFVhB4hPTBYgxCVKkWUlaTk3237x6vSRfv/zUMQNGUGyvb7DCm7fEMfT'
        'Si4OKHaQA1fpeIxlzyjtwO7KwEIkuRhczUZHMPW5g+pFpRqmEh4IMoNff0q7UVHGcwdKhhroEjecltKfNCscHg6Jthmt'
        'en9j/EQ85s7+hNlcoatqgCKcZJjttvblXAt1IKtZYQ5g7Q0iilLTurNAMAv/81LEHRlZWqW+wcaqcHT1EcO1LDhdhM5G'
        'IFF/28EL7CKHYKNejR5SNi/+BRIE1mBwdOi4wZiV3PEo8ee0jVbhlFHrpdZJOvZr7P0W6ESxifaYaa6N9YFFJY1Lbbb8'
        'z5EJQPbhJiQq1XRBId/FlmNDhJms+WpeHqpcNBGNZrq9v5r5X//zUsQtGhmupb55htobv971RRxVaUCYoIwpye5stq9h'
        'mUadmCcGJqD0g0GxRb2nsouq7pTuvZo3z+nta7MLrsuprvd6kKe7ZSoAKS/Vz//beuHgNngsQhQAQwdJA8PMI0KxMRSX'
        'ZQ7eSk9YjB1sKyNKib2M8PnOd3+EU73kcr+PNW01//NQxDoaMc6Jv0kwAAv5/FbLzvrltMz3zI+NH2+/Lm1hvqTDTrWG'
        'VII2uPUCbWK6FKV0dJdbXdXt+p2+EKaClvdUAAEJXYJhYfYMg5x9KYC4BEHE8KlSAMZ9kiaFssusEuAvABVmh9JlIhc2'
        'LoTgjUZrdkQ+QaogGG35eMjBycPEcP/zUsRGLAvibPWPkAHHjWGQFwFornSdIqYqz90EUFj7IOVFkENRoLrqRbSsu+5f'
        'PmxADQqE24700rXTrU61f/zA0IgTZXImXDQqF8+ZmX9f///5OEEMzci5kaE4dNybN0DAqJ7f/////vmJPmhQLRFyfdEB'
        'x9iN1fxZv7JOl26xMjmU//NSxAsagLK4y4lgAMXAwGyMcD5oXGJIJFni6hRIiOiLyYzyFHi1JAvadkDgmDLQwWIh16y4'
        '9aT2P/Z+lKSSSI04qtyDhpd6RxcYLuS2oyU+WFni7BqUuELAkDwkOKKdyxjmoeFk9CgCMWKokoAHfofVRamyTS9qkugi'
        'SoTOvRLs/5T/81DEFxpTwq4TySgAOcHFAMHkEjCylRr1mqKzJehnOUq0WQurIXQ92YqPZdVKqkP31IuR83v++ltFyst+'
        'a9E+/Vf1p3s1aPSStWonRzdur0ZE2l0962qrDYih+S0nRZVyRFIxSRJBv6vFxAuqpE+ZtCeZU3EydQzv1016+RJ08xPE'
        '//NSxCIZ876iXEjFJWuZ1cegOZszA2MZdS/VBXZ3ZB/fKbnRX6tre1vVvrVq1/1Vk6c1Np//v9VL10ctn6dWshnazV3N'
        '9e/fs00M931fipuGCimAABDXU00nMWsHInRbyXoxjfIQTGgwxYoQDSDOm2o+mMbkARfGIEZ8IgRJweUbgnj/81DEMBjQ'
        'oqY+C9IIoJwxc0gHzkXIOcOGtTgQTtNE9fu1YUqAM5TQj61uCuvVTCDo4MjQ+GG1rNN6tGlFM+xb1f/87knBvJQPBSJq'
        'lrErpyUSu+5MOwlkImT1bSyEWl2rXWlSKHWXTqMoGUMB0nJZeOT5yXEMR38252I8d7c3Gvvd//NSxEEpjBagAMsQvIfK'
        'gABqjh55IB96aj0muIGwndlh2PpBepAgAuIRcuMHPzwlX/9T//////X/8fXvf/+ne9x+59jBzyLiih/h3clh2aMBYMFD'
        'FD8gT6oHA6UIF3iX40un3mKf/e5vTuJd/lg8+ZLGKoh+DtWTgBMD0jRWIQCUlw//81LEEBzzVrjKasVR8zb6X629SLeZ'
        't/73S2aYSThO1SWA7AiT9QCMEZVh558PY5Jz/0G1Uvebna/haPiSgbT3wSDhtf6v///////2r1q258xFYkqi6mUzq5ip'
        'ScxlK0ES3aa9+P/xW25hH8T/Gi0Y7pYCN4ncnkExtuc2BsD3VwUF0//zUMQSGNL62x5TBHhL8SBb89PryzfHl45h0qr3'
        'vF77ffIonq5D8pAf6lqcOBgi2Iy3WS691vrpzpKp2Ojl+iEV///////T6P/6I/xg6wqHQu0XY4Epdftd4D0YjXvqkjcb'
        'iJmKCjQ3NehhkMrh4XcRc2/22I8MZ1qqAACXIEE851L/81LEIxnS7tseC8QUpVyBjI739kd/4cUJQcWHUgp3Psqui0Rk'
        'siVuiIdFEs92Tf3NOrof///////+9CG9BgolCKLFrfKpawOpp0VCmKE6zeaqzidu2uXSpvXhZhAjIXJyOKTAnxCgi32x'
        'eBF6YnC271FiZtbreLD4ge19SGG8ufaf0//zUMQxGYmm6lZ7BnJ5HSkkDsJMUGL/PaVSM9V36YkEVMMBhyU80CwvZ///'
        'Z9KltQhq1PeOpSBDxXs/v6nPMhIu1FWkgOXaINQEf74J4ZUaKXcFysXazTbBM2jAhuD2jD7m58bnW3efMr7OfSdUP57k'
        'E4KKzEp8oPzGU1IoAmmv/7f/81LEPxnzLspWekScuezAmIZRgrSkSn/IHKVHMSzC6/////////r7+2QO5QUi1Ve/9FHs'
        'YBmxIJy2IyWiSKE2DH3EXQDaeTPk958sgljg+TzzvAIN3DFXp64NPHy6gJgkWlOcWWRIm4260szV+qq+1X9btev8+5uM'
        'ZJ27pxJg7myjzv/zUsRNGkoS5l4LzA7d/l/lfs8zzkJYuv///69NaVFlD3HW/f/yXK6Vqkb4BSjAo/7UV2HRmFNd+O8B'
        'Gjc7JdSnOptXRaOiVUjDXDZXgi3cbG5YtKC4IK8h80ZvGYoxh5CfZUR3Kl6W+t5mBxbFkcUxqt67rXrOSxmW3///////'
        '///y//NQxFkZs1bE/noFDh0MCBjqoEgow5xYAX+u4FvQFqQCD+ETAxk7BGlJuQWlQQkmDWctp8rIuDfWIciTIgaBgo23'
        'xS7CIsA8CILTBdeJqkdW85DPeYzWfr/JKgzAg+IhAJTSJG8XzIlBkJly9P////6HXRWg+F1gW+rgLVvEH+D0f//zUsRn'
        'F5F+xZ56BO5E+mzJXKOD+NMRQWgnLcpwAiElWZVTN55wtVPY5OErnoOiQUOB0MQ6r6kd30IqtZS9KtR1+vqrFUuzZgE7'
        'EK7ssrNVX2rUxSmyPltXRrIEcWMuagVTb///wnERoFWjqtBaQCju+w0R3m8WsbLFAQhJ0dQDsQqR//NSxH4Zkla4PnpE'
        'tsBFFZQS4sZrNZysl83+EtIBkMqCcKkttR9G1F4Mt87yhnnGnZ5zfM3722dRAodknclR9FIKkQmp6UTtYbEp9CbUyb+s'
        '7q0trRKhpgowedPOHYAXoKr2+w/lbZ4B+klY2I3hjuSKVTqMxOp/mvU08iqJsDIKBKr/81DEjRn5er2eikyWgVUdQsOQ'
        'hKjIbdjZN1bGzHGWhS85VK5nQxXr/Hu+tvoimd5n3PXXMtEIk6yIVAe11jlWjQrmKOhd5zIILKqiKHLd8ipoC5bbaKBI'
        'K6M8YhlHWZCFiki3o25+R5QCf2NPrsZR/z/t8MdJyD0ZDhbKAz52nYKJ//NSxJoaGn61nnjE9lZ4c21I/S33ffZ7385a'
        'rgBUck+Z+bDCSokA73qvJU4sQT0SSMnyhtdqy/kL3IaUN+82orajWiqAN3MObb/YempahBEaJoKhYTLuw2xarOolUGkV'
        'rKiRYX7lsJ9YyNgVFwDCansmaokm3nP/v1EMPCVjkEy0fmb/81DEpxnRjqBeE8wSVIFj4lcVWLLWWVFXgo+UGk4QYHHG'
        'AkkHEyGB07qWJj76G0YRbpoqABXbbUTMpieiADA6IBUBtc6H4cjpS6643v0W5HYlLeL/H8JBIDQfD0hx6LdFh1bvDYy5'
        '//+m7u/Xq720RCIn9PjrmIjn6XGyPKRSWW5I//NSxLQZISq1vkjNBhllQ0WF2Q4NWrouFSyIsesxDalOPazF0eXqAKW7'
        'XetkojLcJCQyu+4QF4eJyEQGsPgI+LCRwYTOQkf0MXYtBNy7LXTh/+/+/cCfjda0+jS7cDMPEIYpHWXhQjYVKVzZTUEu'
        'BIn9jqvGnooOymvWt3sbnNU+MXj/81LExRoR0nh/TEAAtLJyWmJBugCuHVJa9k7o45VMO753H8O91hzWi2afalkUznM7'
        'cUz7n/dZ85vLf/nvD9b/X6x+AXfTAZZFKfWFHrnanp/8X/tTfX6v1uXZ3apE5vSXSWu6NoFqWVsACtD+c3jszqFarkqu'
        'q3UQzGSvIv5XTlNclf/zUMTSKvJecZ+PwABmms+mpfTXK0qqWLdPlWq9kDSVTSl0WIrJiziwc86IUuhxFIwgUMV1LJfF'
        'XyfO13OYGWmkqViQqGLG3CYlL6ty138p7v44Bi0k2hS6RWJyJtYXK8kM3LVrdatT3ZZLq92v+2iNeVgWJMQ/KdZa1zrE'
        'r8O0sBT/81LEmy0qMoZfmMAAps01W9z9cpqUKBUgrBACQ0OFXaxdJKV/301YA31jwDegu5T+Ng8GwrDmgCllO9Zj2YmB'
        'mhSv3ymHccHo6bnLqDy5qoXE43QJhwgRKiOkwS6qybRdTj1mcjF5UsDAzRyBZFaravVOvVQJxIN3lyHV3Ljy7Ccel//z'
        'UMRcKKtuVE3PWAF05zL67bKXUIo0jVRFoX1Tf/hlW5Nzoq85NMiD7F7Y7pzvdvrtBz2WrT55fV09SIvfV2pF8Vf/zJ5T'
        'T5kJKv9TU35f+S4u6imFbG1HbbZ/dJYScVEqhuGF0bMBZ94XYpQojeSt1VprFp+4eOEWoUP2r9n5Zar/81LELhsTAnW+'
        'SMVsmd6WqAQ/aU+neZgjMiYaknD/LlrdzVLScjE0t5ka+v0TpRF9aVtorU3vZFo6+meJZCEQw8nYse6eatWr8vsqAKSq'
        'hRSSsrCp6wqNUFg0IQM4RE11qq4UBVRJaqzN7N4VVUBEqFATKMzN8Pn6qf7M3/8Oxgrhiv/zUsQ3FMFuRBQSRhSVlirq'
        'j2nlQk/1BU763f+dnf+sFa/hqo95U74lTEFNRTQuMKqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq'
        'qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq'
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
        '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'
        'qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqg=='
    ),
    '015.mp3': (  # Left hand selected.
        '//NQxAAOqEJ5f0MQAoAFtSOSSu56IiILeBAAAQEAfPy4e8HwfD/BB0Hwf0cEH9AIBjBD/9BR3/+XAhzg+//Lg+f/5R3/'
        '//E6aYAbjacUlktttckEgbbk4c0ku4QAga+6UTh80EA8tPeLMIoTCwPxhh0zLH1k2CehgEtx0ZJlLaWNAf/zUsQ6KLI2'
        'ml+ZwAKQzSvO5S7v19aSsWJBzv3f5zX41O7obVXdWW2aG1fy1brdmcat3P9drTsMS2ipMae1btZXOSqxqp21T0nyiMXo'
        'csfhzD+YYfrn/v//9//P/ut/SWJZSCgw87/Qr4oQcuwgB1//5z3f2aKRoogNKk1MW1yo1IBi//NSxA0c49LqX49QA7lB'
        '2VN7C+XlXGvCGAqj3jnZxdCkEXEGI5GVCeBUJB4LxwvUREfl1zFeEKnP8/w8JRUGg//M/Qf0LkCqt6tZN+ufZ7yB0Yf2'
        'f+ln/5EOSR0///////9Nnnp////dzOf1/kRaWj5+PWqyMAAAOo11kABkMiE5XHz/81DEDx4KMuY/j2gA+UlMiqwoYIux'
        'SvykYQmDgoMTgtZ83CgQKTHRNTczWfRSQNE1y8UjJYuiVmaDpsY0FRMywgMUVbzdC1Vm9qzCo3qz6Wc2YyUZKQekmaGh'
        '4zT/6Bgktl/zVRm530LucT/V/zyz+37/+taU1YIGEAuUABDm1mv9//NSxAsbeybe389oALsRNy4vm398bwK1W23a0I5j'
        'Zh9nrOly2pIyG40LqKzEkRLQrEHpvrq0lInjd9ek3VpP0UUTx/92/RNkGdJJzpov1GSbalooqf9f////////9FXUZHyp'
        'YcJkuWHEdNXWpnk6FqYIAIGk63J5vXvMQ7YbxNhY2Rj/81LEEx4DZtb+eMVsvhdn4r2plfJ9mgWO5p+suFc7x/r20uXW'
        '/j7q1Eun3b7/4UpnA19byQCVrHIKJEy6tWY4fZFukoVBWbQial5Xe5vyqWuvVk/W39p7V//+Vtujs+GUKVCglCtfcgOJ'
        'WzD7ktr/zBaAAAGNGAP+XvtjoKo2d1aJov/zUMQRHcwWwi5IyuxEPyg82shlvUji83PfDnDKyh1SF7UnfZXb2ZNPx06u'
        '93YzORavOqZK/aLqt3qh2V1tqyMjagOKHnIWckkXYXKPExUQdBRkX/V+t60ZEXRKvOdEbW7K6/+/5HOgcZt1el5EOd5y'
        'IJvVZigwZjcbITKmjloJBoj/81LEDhh0Dtr+KEe0ldUOxXMJ3w8tFu19azoyNjRUp2Qi3p2bZburlfZJxqE8+/qU+f2/'
        'oq9f9ZMLpmeydYagPR/WVHN762A3UBGyZQUTwDnxU99W1Iroe40p7Q/zVMGlaVpBc+lrT8v+kYeGw8jUFiVbF9gt4xir'
        'hC3GkUIBth6cMf/zUMQiGkmy2v1JGABH+eQMSgqlDf1X8oOrQ9qu3lVX/+H9bqss9iPIwoFcEm54qWFSIdcdDQsLEzSl'
        'K1lhINAQ/67tciVypENcjbnt+En31D0ryKp9DP2JP4zn71VVuKGQEQPE2ELhi6j2BGHQJisTEYUQTh254hNMkDaXWoeP'
        'nDf/81LELSWD1pzLj1gANzqhJXYswlHD5hpUeHkkEuq7cgpqpt2e13JMTQYx9zSWbPR0Ylu65k3umV/+i2v5dcXW2r52'
        'V8vimVct/l0uqK/fVxMW7RbVQ7/6/5ZFf39Tbu+uPV+5uH906Iufjnn+v4vvzmNeQTcPkkkbkbkkkkbShOOu3f/zUsQN'
        'HInm7l2GQAK+d27GtigUiRyxEKHHSa2qHoh3P3N3xe802fv3I1tVlq/mqj/5i9u0zRAJBsJgbAwEY76nmoqm/+ZGB4Y+'
        'weGHuOGEcUwVtA1NRguEoWIMspQRp+9AUAZQ4B3CATuzC/oy8XYu5VXesFGOMozePAYTzGAlI9M+//NQxBAZ8a66Vc8Y'
        'AAYpuFDhTz0zeBqPwxmOpQ6RrBQMGp+vqscUewIxYOAGLFH5GW9XZHIhZIf2fLPMpDOKCHqEJVTrsBPkn2iUNyze8i3q'
        'V2Kbhpw8NTolX65XlssQaCv+Cq1TtjAOVzUj2OXdrZN80/xxIZpsAgiQFiWcXkAgjP/zUsQdGVletu7Jhoy7i4QSBzw7'
        'u3+3IGb9ozX8/Y2nQj0oFcmPIzU7SUzh4mTLQfUdIhMBCU6YCAGMS4BtekZf3at+2//yiwgFzh70obRSzzKhJ/IKz9AI'
        '3sAsSaF8eNCxNbTMljkDmb/KH8vO1bIAAIJkfdwAlk0yD4ZEMghenppk//NQxC0ZiQrKVg4MENM+3jGQYhysu68YoCOh'
        'EDlxBu/TFgyUf+TYXC0U////6z8QE0rPhhOrkKJdbyYnEAwIBhAnPwfiB1XJIEBxQYMv+bEhWfYlAxWXqc4s42kwCR5O'
        'EtP1KmQd8ic91+9xkFZviN3S6kwRZLpLjXLlWRWHdqV2///zUsQ7GOIazk55hLi66Kqsz2p/l37K58Gxor////640Inn'
        'tcSBGE3HntOIRAbRU2k4shMxVeuU5EAz4T/1DFHHzKBiPp45hUoPN2s1sxuVrRAgCAX7CS5xgcQAjj5DkLKNzd2zST0J'
        '9uxz2Itt2/p19EoKzVYfd6Tc9cxvJmZlK4iZ//NSxE0YWiLRtnnHGosNDaT1/9n//isrEUn/vmrqq66t6q0ylJCAyzdy'
        'ynlHVgJXhYEitzqwYk5hrOwpzG85I1GHJK+ABHHJnYQG/wp0rvLW0WovDOFuqhT8fz8S4wdx39f6+XgJyPp4/r069G6f'
        '1/1//////u3avYlLEsivnHbbLaL/81DEYRlbas5Ww8rmiv13vTWEom/RaejtqtcxHeS4dplc/xjoDMh8INxmSStfYfgw'
        's5mLKPe4DTOSRN+cmwfGYUfQ/TVOo7AYEW4i+nR9Wyt3JSx4eF0ufk6dWyk0PoX+X3//////+3o/0dHFna4x4rnp3oUa'
        'AGdivxkqi4o5tJCJ//NSxHAYo1LKNnoLBkL0hpyn0MWkJXIdSExYngsJ0xa3AbZkN/jJd57GgENWijtejn/aR6lbBEMh'
        'jW3zP10RylLwd4KDFGf/dgrLMUSe/JLnuiqa6vHsfpI/O2/+VKm2laftel3hAAAXiObibiIPJEsQbnTAmpTh9JnVa/U3'
        'S6VUGlz/81LEgxjqAqhWeYTuIbMrfT/dmLL/////0//////r+T/Ql+b//k+Bc+EGi9xSacVy6JN5AogoH9zdO9kAvODw'
        'kXPeEFz4FDJ69E++pMnAyerhgRjKFMrhRk30ft///9f//+X////+WimNcF94C+eY2Usn+71lOxhfbvc2+V6+L27TDf/z'
        'UMSVGJPWoAJokT2XvzlKVJHnKpYVyuhYhgTW3RiIkEQwRMHB6E4/rJXrNSHBVCsqAYdTIgQSCWsAgagmA8RzzFwgA0KB'
        'Pshg0q3jKs4ZbdhRnBIERQVFHL1+c2+xWg9//Ij9meess/FnM3/KW2K+3aqxrUS+9X/atm3XRpEOhkj/81LEpyEkFrAA'
        'EFkckMuKYiKeRF5w4OkwcD2QqHchOTCupaR3LQCyYfiQ2II7wvHLZfRsccm4hssjmjQytKoO3koUoiwgRHZSaZOWqr0C'
        'FezZvqurru8uh6q262YiI4EdfAtbrRA5u+rYIRQQxJZSSPu3FiWqzI7iZ4S6vqI7Gd/6dv/zUMSYG5QWyAoAWcRf/+uT'
        '///////oq/+/Xv7qRzCRqJK+xVQkXNIVUuNFSmEGChERWodDgKQYJgIYHjYtR7iCKniHd5iZj/aDosRRQpbFiYIgxVQY'
        'AED0PyEZLcUp5jMIGxT0nOjz3z1HHEff8R/911fE3XxU20DBpkP8Sv99RP//81LEnhdTsup4QAtmXxX//u67fSsnq5GO'
        'pbozKjvq5THQrLMQgcp3PGAhm39h+tpLUenj+yaBrGsG+qkMYVHBny+VCLVygliUy/L8PxFrSgHOzm4daUJsodNE5RCT'
        '/rBRgq05IrDbu88WqjkFMZU/t8ze/R02lLsyLZDicKZO3emiS//zUsS2GGOy9xhABeb/0a/lQ11PLEmPOiKLnYilTrFH'
        'sqd01VhmZdv9bGuR5QXXVMAHzTho9OBNiJxEMGfF4VODDFY+b6MAdzIhYxMEKoOYSpnsCxooKBjllAYsATTULA3yRKGS'
        'BEycxcYQArBKfER5uoibIPzIoVJQ++sbL1pqN7yI//NQxMoaic7ufHpFChAEDbNLNtHmrT3sq1qc0SH6lia0YFHDYImh'
        'tdvc24Zexln3/PWXKLuHwTMtFilSYR2/1X43//j5////TWpJqqzUj9IGi/+vyRACGp3KUKpnDOA9WtxfJshmChIwOaYK'
        'XyWDeKBrGdtVIBMr9hd74AUVP/XLNf/zUsTUJtm61vzeUs7/hZLkoIH+MNNf/Zsp//szGlG/Srzsbnmq04DEseFj2Crk'
        'pN36Po2e1/2eyoULEkJqeRC3RUFNGJdWK66BiKOS3RONJf+/03ZhlBR6fFrAYVc09yNNOrQqWwGtmxU7hHlgXtprOsTd'
        '5chF28W5q3miHj3Jr0HJ//NQxK4c8ba6fMpHCLTrf3v6yGua8yY/058VVzDtcLCU6Fk20v/9tPnfu3Sz3Ld4hWM8bqky'
        '7u2o/KvoYgKiKsrKgIPNVfqp7qUrnf+vYK6Lct8qSxobOIJmoAQwh3lJtofbz8pC9/aQrk3SR5bOhi1c74gdluSn/+/o'
        'Uf1t1O/vav/zUsSvGkGyzl7CRwaursOHiAAEMdzu5FMRbf/////////1///f19GfscdRokggP9b0P/X3FuRavSS1pwmJ'
        'grQmoITjtBJd1YfprE9y1emHfnLe8qFJNTCHYpAb91c7DpsTpofv8AxZ0U4AqLJf05PO/kYnTDaScvNRNKKaOUl0igGE'
        '//NSxLwZc7K+XsJK6sKOVAwylkNhNBRwMNoLQI0gqIAiQ/9u/+K1C3rq7//VpqIGAQLaQqAB+t/1t5fM5ZOQ91LKbEqI'
        'vO9Zv11Uot3L49P//5yrfMvrymWsNeVJcQWQ3ZtXiCpV10dfUEubb1XGQ1LbhIJKIC57jzlBEFTsVyWa0Yn/81DEzB2x'
        '+r2UwJNIvGf0gEJnZwFKGEl0hLnub0JSSZwGVJDSoFuhrJG6ySrHjgIRCUACF4/r8nIlUd+d237a6XxfX+qol2tzuzvL'
        'X5xBQ0/8klzPRHafq8Mg3PxwWk+8woAJqIPhnI+pCUcxNW8z9atQUp8zL/03Urq823////////NSxModEiLKXsKTaf/+'
        'n29jO0Hq6jufEpfTJb+1pigVjJLPyWu3nySsdDTfj2VaecFM2mS7ng5XwAY2v10nBloDvXCzV8+qJVHgukV3QXwQM7sg'
        'YD1UU3ON9uVvUnhXzoOTLPoZP/OLt6KD4sAs9//u/9NYazqw0HysXvkWQoeo/oz/81DEyxlbTtp+esUJktACoktS8l/j'
        '5XJkqn3fPn29WweSOfzXVtGdmbk+TJ1Bjxlwh7mjUWvTRNLRgq+7YKSqxhX8jfAwlSH9unDUv//US1JjCqx0BOiJBETC'
        'J5YGq1fLC5yKmtnZ//Xg0HjIMkcsDB5mvQPnYqDYafyMlZDAy7JP//NSxNoZagreVniNNuLnSiQ2loacYocloSmZocC6'
        '6Yq1pDJu/zmGuiR3uEA/4GixJI6Beao4FQVyUbJ5jZpu4ToUOEartVUccvPyaKy7RbgwjFVylzeUuYyDswKaM6mE/8pq'
        'yfzzBGQDFemlNq9lhV5Q88aRuWxr+JZt3l716MKzsj//81LE6huprsG2eYcK7fCnQxuV1dOalxuCRi24sjGmYMOmyUN8'
        '+IscwkrfyMSr3Ps5KZQKnf0kVek6ljz45eSWZWciE8wzbeedqfQxStgIUgICgxNApdHNq1S0xPt7eRjJVURsQAjLgDj7'
        'vDKVPUBO9Vib5wO/W1UoFOXaz5+sLmAy/P/zUMTxHWKCnNZ6BRYwuocej0d6Ma4WznUruzO3AUHPealaC9QqfbtPIDkt'
        'YO4d7gTDQxPFBDSeROOP7d1utrz69xE7K+HdVX189zUa9UxI04KFF1FmHhKfc0vFVvWx8mJ1CobomI04uKE3pFTTRcYP'
        'Yh6Uqpuc/FEf6fWqKEY0kjn/81LE8BvScpDWeYUuY42hIchkAwIPJpIQi4TTlgQtvDVooOBSFsQghCvNzAeygFIOuVPK'
        '/OBG0klFCodbhbcpHkJQX2+app5Pplfqi8fFmBTb/3XOesnOq21D2drtfNbvY3x8+vvuP1HO8jqQyDjrXNYMGJlS/O/v'
        'f3umtdEGQcakQv/zUsT2HomqfL9PWAAck4oCXoezuF2Jwg+DW2G6PSiu////////jxVezw38c0zTVcSnVkTxq6fb8aF2'
        'aN5bWff/////////+BEjnQydWRPAeeVXs7Jrbx5Ehb3aFb2hVrBER6qIJsjWBBESku/V5IyBoVAKdz4IECspyUFpCQx5'
        'DvuU//NQxPE0g/KmX494AO7L6a9hlfvZaSalGC08v/4VhxToQXWMRkfTT7IURd8v8qj638sj/L7k4sEVkns9bEDrRwm3'
        'IUzxX+dOlbqdUjY9SNrfZl3BxNWIgub+yTXff+1kjYhRkqloTogPtH9QkyXwkNcjwpdZVt92qJf40843mseDQv/zUsSU'
        'Gcm2tn/YGAAJfy3r+vTmHiHtZtNU9//In8I1HJs2scEFgk6J//n96nPl/P9m6jgkrbBdX1f/1pqRHlZESz0l//WqgTlZ'
        'Sclt3zViPJOD0IctFmN1Qqw7ixDoOBYAJoyzUZKa+dSUSxi36pbuRg9W90LedxiiwIYWWdv+/90T//NQxKIZSl7mXkmG'
        'vmV2IHSzRMWZqS6NKrbK9k/tYWDvZXf2dlHqoVBKdp1IX+LrHKPtXPHwHcAZLYm7dthVvw+dLwbJjYZjqbkWC4Iqpsop'
        'uoTseTapm0lSKjVYPBL8ZWeV5hIGUREBoNKilN/9b68yzjjB6FB1ylJXLEQAVcAgqP/zUsSxGWpCtR55ipKh8gNQ7cRU'
        'EZV7VXPe5o5rrqYTnjFoNq0pc9j7SyqVOVFOSyQezLo0h/KhgTyzidTajPSBG40e0alJhAiO0WBIxjgvu5Xo41yulllZ'
        'UVpjCQOOES1EnVvpXSaNm6rdVopGZjDDd1ZizG5CCKD0oQ+tguNSrvSq//NSxMEaCeK5vkjK7hokp1ulIGrVz/iu2pV+'
        'XWSbfXafrIg8GweRLMSd4ExbWBIjYWITAPwYHCg8aHzrS6XVNMl3N1DBWyRUsVk62u+a1goWHCJUXWvc/rr6VXXNd50H'
        'mhg8JzYJtU7XbNrtYWvF6b+7H7NeY6Za+16U62nbaEVM9mr/81DEzhk6IpUeeYqSqI8Myfzw8igCEJZas6zPqEPsXBPh'
        'flyP4dZxlgJszzObmflBJjnPGm8E4nfgtSWE6+tvUPfRFRdXLu0JRMWNrLtQl/Z1LYnpyILFfJfNWdgmcG+OhbEzxYrp'
        'iXH/9d4xuBEZIcd/IyKBmXK+jHyfMcV8cP39//NSxN4ZQZ6FH0lAAH////ljs+KRM7v/+FWT4eR+JkpDvXnJsmcon///'
        '////+6Z3Hxqn3fftT0qp2mNiWC7UDx5d5HUH///////////+6a1//9f///2TigPw/2ddv3OJd/L/E94imltu30rQKTnu'
        '2CgjZZzXJodohjF7fnahvrqYQzr/81DE7zRsDpp/j3gAAQEKIKo7WYijYUgpi6TN+UrbzGSul/0veOkrOQ7KUK8wYUaZ'
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
        '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'
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


if __name__ == "__main__":
    logging.basicConfig(level=logging.INFO,
                        format="%(asctime)s %(levelname)s [%(threadName)s] %(message)s")
    logging.info("Build: refined-bilingual-v16")
    app = AntiTriggerFingersApp()
    app.mainloop()
