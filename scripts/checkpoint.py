"""Save the named, tested snapshot while the Lean worker keeps its Git directory read-only."""
from pathlib import Path
from hashlib import sha256
import json
import os
import subprocess
import sys
from uuid import uuid4

root = Path.cwd().resolve()
queue = root / ".work" / "checkpoints"


def git(*args, **options):
    return subprocess.run(["git", "-c", "core.hooksPath=/dev/null", *args],
                          cwd=root, **options)


def source(name):
    path = Path(name)
    allowed = (path.parts and path.parts[0] in {"FLatticePaper", "checks", "docs", "audit"}) or (
        len(path.parts) == 1 and path.suffix in {".lean", ".md"})
    if (not allowed or path.is_absolute() or any(p.startswith(".") for p in path.parts)
            or not (root/path).is_file() or (root/path).resolve() != root/path):
        raise ValueError("Expected an existing source or research note in this campaign: " + str(name))
    return root/path


def request(message, paths):
    if not message.strip() or not paths:
        raise ValueError("A commit message and explicit paths are required")
    records = {p: sha256(source(p).read_bytes()).hexdigest() for p in paths}
    key = uuid4().hex
    target = queue/(key+".json")
    staged = target.with_suffix(".tmp")
    staged.write_text(json.dumps({"message":message, "files":records}) + "\n")
    os.replace(staged,target)
    print("Requested", key, "for", len(records), "files. Receipt in .work/checkpoints/" + key + ".txt")


def land(req):
    data = json.loads(req.read_text())
    files, msg = data["files"], data["message"]
    if not files or not isinstance(msg,str) or not msg.strip():
        raise ValueError("Empty checkpoint")
    if git("diff","--cached","--quiet").returncode:
        return  # An operator has staged something else.
    for name,digest in files.items():
        if sha256(source(name).read_bytes()).hexdigest() != digest:
            raise ValueError("File changed since request, please refresh: "+name)
    git("add","--",*files,check=True)
    try:
        for name,digest in files.items():
            staged = git("show",":"+name,stdout=subprocess.PIPE,check=True).stdout
            if sha256(staged).hexdigest() != digest:
                raise ValueError("Index content changed during staging: "+name)
        git("diff","--cached","--check",check=True)
        if git("diff","--cached","--quiet").returncode:
            git("commit","-q","-m",msg,check=True)
    except Exception:
        git("restore","--staged","--",*files,check=True)
        raise
    return git("rev-parse","HEAD",text=True,stdout=subprocess.PIPE,check=True).stdout.strip()


def process():
    for req in sorted(queue.glob("*.json")):
        try:
            result = land(req)
            if result is None:
                continue
        except (ValueError, OSError, subprocess.CalledProcessError) as error:
            result = "Pending author-side save. " + str(error)
        req.with_suffix(".txt").write_text(result+"\n")
        req.rename(req.with_suffix(".processed"))


if __name__ == "__main__":
    if root != Path("/home/nitro/flattice-lean") or (root/".git").is_symlink():
        sys.exit("Run from /home/nitro/flattice-lean on sandbox")
    queue.mkdir(parents=True,exist_ok=True)
    if sys.argv[1:] == ["land"]:
        process()
    elif len(sys.argv)>=4 and sys.argv[1]=="request":
        request(sys.argv[2],sys.argv[3:])
    else:
        sys.exit("Usage: checkpoint.py request 'message' path [...], or checkpoint.py land")
