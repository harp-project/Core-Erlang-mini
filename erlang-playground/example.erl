-module(example).
-compile(export_all).

f() ->
  Pid = spawn(example, g, []),
  exit(Pid, normal),
%  exit("alma"),
  io:fwrite("Hello world").

g() ->
  io:fwrite("Hello world")
  .
