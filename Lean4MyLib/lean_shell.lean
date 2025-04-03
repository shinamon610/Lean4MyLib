import Lean
namespace lean_shell

-- 参考元
-- "https://zenn.dev/labbase/articles/e9ec297ece34b0"

open Lean Elab

elab "#hello":command=>do
  logInfo "hello"

#hello


elab "#shell_ls":command=>do
  let spawn_args:IO.Process.SpawnArgs:={cmd:="ls",args:=#["-l"]}
  let output<-IO.Process.output spawn_args
  logInfo output.stdout

#shell_ls

elab "#shell" s:str+ :command => do
  let cmds:=s.map TSyntax.getString
  let (cmd,args):=(cmds[0]!,cmds[1:])
  let cmd:IO.Process.SpawnArgs:={cmd,args}
  let output<-IO.Process.output cmd
  logInfo output.stdout

#shell "less" "flake.nix"

-- 参照している環境が違うっぽくて、普通にpythonってやっても見つけられない。
-- 絶対パスだったらできる。
#shell "/nix/store/r8kkr8s0cvzq2zky45agi83mgl6s0zc4-python3-3.12.9/bin/python" "a.py"
