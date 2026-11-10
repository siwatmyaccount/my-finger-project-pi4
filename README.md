# my-finger-project-pi4

**รุ่นล่าสุด: `refined-bilingual-v16`**

รุ่นสำรองที่เคยทดสอบบน Raspberry Pi 4 คือ `stable-last-crop-v5` จาก ZIP วันที่ 2026-09-12 และอยู่ในประวัติ Git

โปรเจกต์ฝึกกายภาพมือด้วยกล้อง OpenCV และโมเดล TensorFlow Lite แสดงจุดโครงกระดูกมือแบบเรียลไทม์ พร้อมระบบจับเวลา รูปตัวอย่าง รายงาน และเสียงประกอบ

## ส่งต่องาน

- จุดเริ่มแก้โปรแกรมคือ `src_code/main.py` รุ่น v16. มีหน้าฝึกและรายงานไทย/อังกฤษ การ์ดขนาดคงที่ ปุ่มปิดสีม่วง และการ์ดรายงานความสบายของมือกับความก้าวหน้า
- เสียงไทยอ่านจาก `src_code/Voices/` ส่วนเสียงอังกฤษ 17 คลิปฝังใน `ENGLISH_VOICE_CLIPS` ใน `main.py`. ทั้งสองภาษาเล่นผ่าน `mpg123` ซึ่งสคริปต์ติดตั้งให้แล้ว
- ตรวจไวยากรณ์ Python, ทดสอบขนาดการ์ดบน Windows ที่ 1024×600, 1280×800, 1536×864 และตรวจว่าอ่านคลิปอังกฤษทั้ง 17 คลิปได้
- ขั้นต่อไปคือลองบน Pi 4 จริงด้วย `./run.sh` แล้วเช็กหน้าจอ กล้อง การนับเวลาระหว่างเปลี่ยนท่า และเสียงลำโพงทั้งสองภาษา

## ติดตั้งบน Raspberry Pi 4

ชุดติดตั้งเตรียมไว้สำหรับ Raspberry Pi OS แบบ Desktop 64-bit (`aarch64`) และกล้อง USB ที่ระบบมองเห็น ต้องมีอินเทอร์เน็ตตอนติดตั้ง เปิดโปรแกรมจาก Terminal บนหน้าจอ Pi เพื่อให้แสดง GUI ได้

Repository นี้เป็น Public ทุกคนเปิดดูและดาวน์โหลดได้โดยไม่ต้องเข้าสู่ระบบ

- ลิงก์แชร์โครงการ: https://github.com/siwatmyaccount/my-finger-project-pi4
- ดาวน์โหลด ZIP: https://github.com/siwatmyaccount/my-finger-project-pi4/archive/refs/heads/main.zip

คัดลอกลิงก์จากแถบที่อยู่ของเบราว์เซอร์เพื่อส่งต่อ หรือดาวน์โหลดผ่านปุ่ม Code → Download ZIP

```bash
git clone https://github.com/siwatmyaccount/my-finger-project-pi4.git
cd my-finger-project-pi4
chmod +x install_pi4.sh run.sh verify_pi4.sh
./install_pi4.sh
./verify_pi4.sh
./run.sh
```

หากสคริปต์เพิ่มผู้ใช้เข้ากลุ่ม `video` ให้รีสตาร์ตหนึ่งครั้งก่อนรัน:

```bash
sudo reboot
```

แอปเลือกกล้อง USB ให้อัตโนมัติ หากต้องระบุกล้องเอง ให้ใช้ `v4l2-ctl --list-devices` แล้วรัน เช่น `CAMERA_DEVICE=/dev/video1 ./run.sh`. สคริปต์ `verify_pi4.sh` ยังใช้ `/dev/video0` ในการตรวจกล้อง

## รันพร้อมบันทึก log

```bash
cd ~/my-finger-project-pi4
source .venv/bin/activate
cd src_code
python -u -X faulthandler main.py 2>&1 | tee tracking.log
```

เมื่อทำงานถูกต้องควรเห็นข้อความประมาณนี้:

```text
Build: refined-bilingual-v16
Camera /dev/video0: backend=V4L2, negotiated=320.0x240.0
Created TensorFlow Lite XNNPACK delegate for CPU
```

## ไฟล์สำคัญ

- `src_code/main.py` — โปรแกรมหลัก
- `src_code/hand_landmark.tflite` — โมเดลตรวจจุดมือที่โปรแกรมเรียกใช้
- `src_code/hand_landmarker.task` — โมเดลสำรองสำหรับแยกมือซ้าย/ขวาและค้นหาฝ่ามือ
- `src_code/pictures/` — โลโก้ ภาพหน้าจอ และภาพตัวอย่างท่า 1–5
- `src_code/Voices/` — เสียง `001.mp3` ถึง `010.mp3`
- `requirements.txt` — รายการไลบรารี Python
- `install_pi4.sh` — ติดตั้งแพ็กเกจและสร้าง `.venv` ใหม่สำหรับ Pi
- `verify_pi4.sh` — ตรวจกล้อง สิทธิ์ ไฟล์ และไลบรารี
- `run.sh` — เปิดโปรแกรม

