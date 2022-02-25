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


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

h() ->
  Pid = spawn(example, j, []),
  Pid2 = spawn(example, i, [Pid, self()]),
  process_flag(trap_exit, true),
%  link(Pid2),
  timer:sleep(1000),
  exit(Pid, alma),
  receive
    P -> io:format("Main received : ~w~n",[P])
  end,
  ok
  .

j() ->
  io:format("j : ~w~n",[self()]),
  timer:sleep(10000).

i(Pid, Ph) ->
  io:format("i : ~w~n",[Pid]),
  process_flag(trap_exit, true),
%  link(Pid),
  receive
    P -> io:format("Received : ~w~n",[P])
  end,
  io:format("Process j: ~w was not killed!",[self()]).

fv0() ->
  Pid = spawn(example, fv, []),
  timer:sleep(10),
  exit(Pid, kill)
  .

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% EXAMPLE VS DOCUMENTATION %%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% https://www.erlang.org/doc/reference_manual/processes.html#receiving_exit_signals %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
fv() ->
  timer:sleep(3000),
  io:format("Process j: ~w was not killed!",[self()]).

main() ->
  Pid2 = spawn(example, sub, [self()]),
  link(Pid2),
  process_flag(trap_exit, true),
  timer:sleep(1000),
  exit(Pid2, kill),
  receive
    P -> io:format("Main received : ~w~n",[P])
  end,
  ok.
sub(Ph) ->
  link(Ph),
  process_flag(trap_exit, true),
  receive
    P -> io:format("Received : ~w~n",[P])
  end,
  io:format("Process j: ~w was not killed!",[self()]).
