-module(e).
-compile(export_all).

f() ->
  Pid = spawn(e, g, []),
  exit(Pid, normal),
%  exit("alma"),
  io:fwrite("Hello world").

g() ->
  io:fwrite("Hello world")
  .


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

h() ->
  Pid = spawn(e, j, []),
  Pid2 = spawn(e, i, [Pid, self()]),
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

fv() ->
  timer:sleep(3000),
  io:format("Process j: ~w was not killed!",[self()]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% EXAMPLE VS DOCUMENTATION %%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% https://www.erlang.org/doc/reference_manual/processes.html#receiving_exit_signals %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

main() ->
  Pid1 = spawn(e, sub1, []),
  Pid2 = spawn(e, sub2, [Pid1]).

sub1() -> 
  process_flag(trap_exit, true),
  Pid = receive
           Pid -> Pid
        end,
  link(Pid),
  receive
    P -> io:format("sub1 received : ~w~n",[P])
  end,
  io:format("Process sub1: ~w was not killed!~n",[self()]).

sub2(Ph) ->
  Ph ! self(),
  timer:sleep(1000),
  process_flag(trap_exit, true),
  link(Ph),
  exit(Ph, kill),
  receive
    P -> io:format("sub2 received : ~w~n",[P])
  end,
  io:format("Process sub2: ~w was not killed!~n",[self()]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%% counterexample for dropping exits %%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

h2() ->
  Pid = spawn(e, j2, []),
  Pid2 = spawn(e, i2, [Pid, self()]),
  timer:sleep(1000),
  receive
    P -> io:format("Main received : ~w~n",[P])
  end,
  ok
  .

j2() ->
  %io:format("j : ~w~n",[self()]),
  process_flag(trap_exit, true),
  timer:sleep(2000),
  io:format("Process j2: ~w was not killed!",[self()]).

i2(Pid, Ph) ->
  %io:format("i : ~w~n",[self()]),
%  link(Pid),
  unlink(Pid),
  process_flag(trap_exit, true),
  exit(Pid, alma),
  receive
    P -> io:format("Received : ~w~n",[P])
  end,
  io:format("Process i2: ~w was not killed!",[self()]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% THIS IS NOT A COUNTEREXAMPLE
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

main2() ->
  Pid1 = spawn(e, sub3, []),
  Pid2 = spawn(e, sub4, [Pid1]).

sub3() -> 
%  process_flag(trap_exit, true),
  Pid = receive
           Pid -> Pid
        end,
  unlink(Pid),
%  receive
%    P -> io:format("sub1 received : ~w~n",[P])
%  end,
  timer:sleep(2000),
  io:format("Process sub1: ~w was not killed!~n",[self()]).

sub4(Ph) ->
  Ph ! self(),
  timer:sleep(1000),
%  process_flag(trap_exit, true),
  unlink(Ph),
  exit(Ph, alma),
  receive
    P -> io:format("sub2 received : ~w~n",[P])
  end,
  io:format("Process sub2: ~w was not killed!~n",[self()]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% THIS IS NOT A COUNTEREXAMPLE
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

fv3() ->
  process_flag(trap_exit, true),
  exit(self(), normal),
  receive
    P -> io:format("~w received", [P])
  end,
  ok.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

main3() ->
  Pid1 = spawn(e, sub5, []),
  Pid2 = spawn(e, sub6, [Pid1]).

sub5() -> 
   timer:sleep(2000),
   throw(kill).

sub6(Ph) ->
  timer:sleep(1000),
  process_flag(trap_exit, true),
  link(Ph),
  receive
    P -> io:format("sub2 received : ~w~n",[P])
  after
    5000 -> ok
  end,
  io:format("Process sub2: ~w was not killed!~n",[self()]).
  
%%%%%%%%%%%%%%%%





