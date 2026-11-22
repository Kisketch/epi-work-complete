#!/usr/bin/env bash
set -u
echo "== DIRECT =="
curl -sI -m 10 https://releases.lean-lang.org/lean4/v4.35.0/lean-4.35.0-linux.tar.zst | head -3
echo "== PROXY =="
curl -sI -m 10 -x socks5h://cage:50b3546b0323a35546a24203cf98a4a05f830f4681a45a3e@127.0.0.1:17896 https://releases.lean-lang.org/lean4/v4.35.0/lean-4.35.0-linux.tar.zst | head -3
echo "== DOWNLOAD DIR =="
ls -la "$HOME/.elan/tmp" 2>/dev/null || ls -la /tmp 2>/dev/null | grep -i lean | head -5
echo "== CHILDREN =="
pgrep -aP 28976 || true
ps -o pid,etime,pcpu,comm -p 28976 || true
echo "== DIAG DONE =="
