import pyperclip
import re

s = pyperclip.paste()
res = []

for m in re.findall(r"info \"([^\"]*)\"", s):
  res.append(f"check \"{m}\".")

pyperclip.copy("\n".join(res))
