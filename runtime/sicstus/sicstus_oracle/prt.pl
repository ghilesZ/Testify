% Path-oriented Random Testing implementation
% Author : Arnaud Gotlieb -- INRIA Rennes Bretagne Atlantique - Simula Research Laboratory
% Ref: Path-oriented random testing, A.Gotlieb and M. Petit,  Proc. of workshop on Random Testing RT'2006,
%        Constraint reasonning in path-oriented random testing, A. Gotlieb and M. Petit, Proc of COMPSAC'2008
%        A. Gotlieb and M. Petit. An uniform random test data generator for path testing. Journal of Systems and Software, 83(12), Dec. 2010.
% Dates : Feb. 10th, 2010
%              Dec. 9th, 2021
%              Jan. 27th, 2022: Adaptation for Testify

% Requires SICStus Prolog 3 (or higher) but only tested with 4.7.0 on WinXP
% Portability issue : lists:nth1 in Sicstus4, lists:nth in Sicstus3
% Validated using SICStus Prolog 4.7.0

:- ensure_loaded(library(lists)).
:- ensure_loaded(library(ordsets)).
:- ensure_loaded(library(samsort)).
:- ensure_loaded(library(random)).
:- ensure_loaded(library(clpfd)).
:- ensure_loaded(library(mutdict)).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% API
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Generate at random a list of LEN integers, which are ranked in some order, using GRAIN to initiate the random gen. - Using samsort and sort
% sicstus_increasing_list/3 (+int LEN, +int GRAIN, -var L)  L is instantiated to a list of LEN random int in increasing order, random is initiated with GRAIN
% When Min and Max are unspecified, return integers from -2**31..2**31-1
% sicstus_increasing_list/5 (+int LEN, +int GRAIN, -var L, +int Min, +int Max) L  is instantiated to a list of LEN random int in Min..Max in increasing order, random is initiated with GRAIN
% sicstus_decreasing_list/3 and sicstus_decreasing_list/5 are identical to ***increasing*** but return the list in decreasing order
% sicstus_increasing_strict_list/3 and sicstus_increasing_strict_list/5 are identical to ***increasing*** but add the constraints that all list element shall be different.
%  Beware that the return list may be smaller than the one specified (LEN) because it is impossible to satisfy
% sicstus_alldiff_list/3 and sicstus_alldiff_list/5

% Examples
% ?- sicstus_increasing_list(10000, 1, RES).                                                  % OK  - less than 1sec CPU
% ?- sicstus_increasing_list(1000000, 1, RES).                                              % OK - less than 1sec CPU
% ?- sicstus_increasing_list(10000000, 1, RES, -100000, 100000).           % OK  - 100,000,000 in less than 1 minute CPU
% ?- sicstus_decreasing_list(50000, 1, RES).                                                 % OK  - less than 1sec CPU
% ?- sicstus_increasing_strict_list(100, 1, RES, -20, 20).                             % OK  - returns a list of 41 elements [-20, -19, ..., 20]
% ?- sicstus_increasing_strict_list(100, 1, RES, -60, 60).                             % OK  - less than 1sec CPU
% ?- sicstus_decreasing_strict_list(10000, 1, RES, -100000, 100000).      % OK  - less than 1sec CPU
% ?- sicstus_alldiff_list(1000000, 1, RES).                                                       % OK - 1,000,000 in less than 1 sec. CPU
% ?- sicstus_alldiff_list(10000000, 1, RES).                                                     % OK - 10,000,000 in less than 1sec CPU in compiled mode

sicstus_increasing_list(LEN, GRAIN, RES) :-
        (\+((integer(LEN),var(RES),integer(GRAIN))) -> (write('Sicstus: Innapropriate call to API'), fail) ; true),
        sicstus_increasing_list(LEN, GRAIN, RES, -2147483648, 2147483647). % signed 32 bits - -2**31..2**31-1
sicstus_increasing_list(LEN, GRAIN, RES, Min, Max) :-
        (\+((integer(LEN),var(RES), integer(GRAIN), integer(Min), integer(Max), Min =< Max)) -> (write('Sicstus: Innapropriate call to API'), fail) ; true),
        lists:length(L, LEN),
        Max1 is Max+1,
        setrand(GRAIN),
        random_gen(L, Min, Max1),
        samsort:samsort(L, RES).

sicstus_decreasing_list(LEN, GRAIN, RES) :-
        (\+((integer(LEN),var(RES),integer(GRAIN))) -> (write('Sicstus: Innapropriate call to API'), fail) ; true),
        sicstus_decreasing_list(LEN, GRAIN, RES, -2147483648, 2147483647). % signed 32 bits - -2**31..2**31-1
sicstus_decreasing_list(LEN, GRAIN, RES, Min, Max) :-
        (\+((integer(LEN),var(RES), integer(GRAIN), integer(Min), integer(Max), Min =< Max)) -> (write('Sicstus: Innapropriate call to API'), fail) ; true),
        lists:length(L, LEN),
        Max1 is Max+1,
        setrand(GRAIN),
        random_gen(L, Min, Max1),
        samsort:samsort(L, RES1),
        lists:rev(RES1, RES).

sicstus_increasing_strict_list(LEN, GRAIN, RES) :-
        (\+((integer(LEN),var(RES),integer(GRAIN))) -> (write('Sicstus: Innapropriate call to API'), fail) ; true),
        sicstus_increasing_strict_list(LEN, GRAIN, RES, -2147483648, 2147483647). % signed 32 bits - -2**31..2**31-1
sicstus_increasing_strict_list(LEN, GRAIN, RES, Min, Max) :-
        (\+((integer(LEN),var(RES), integer(GRAIN), integer(Min), integer(Max), Min =< Max)) -> (write('Sicstus: Innapropriate call to API'), fail) ; true),
        lists:length(L, LEN),
        Max1 is Max+1,
        setrand(GRAIN),
        mutdict:new_mutdict(DICT),
        random_gen(L, DICT, Min, Max1),
        mutdict:mutdict_size(DICT, LEND),
        complement_sorted(DICT, LEND, LEN, Min, Max1, 1000, RES).   % Max 1000 attempts to complement the list

sicstus_decreasing_strict_list(LEN, GRAIN, RES) :-
        (\+((integer(LEN),var(RES),integer(GRAIN))) -> (write('Sicstus: Innapropriate call to API'), fail) ; true),
        sicstus_decreasing_strict_list(LEN, GRAIN, RES, -2147483648, 2147483647). % signed 32 bits - -2**31..2**31-1
sicstus_decreasing_strict_list(LEN, GRAIN, RES, Min, Max) :-
        (\+((integer(LEN),var(RES), integer(GRAIN), integer(Min), integer(Max), Min =< Max)) -> (write('Sicstus: Innapropriate call to API'), fail) ; true),
        lists:length(L, LEN),
        Max1 is Max+1,
        setrand(GRAIN),
        mutdict:new_mutdict(DICT),
        random_gen(L, DICT, Min, Max1),
        mutdict:mutdict_size(DICT, LEND),
        complement_sorted(DICT, LEND, LEN, Min, Max1, 1000, RES1),   % Max 1000 attempts to complement the list
        lists:rev(RES1, RES).

sicstus_alldiff_list(LEN, GRAIN, RES) :-
         (\+((integer(LEN),var(RES),integer(GRAIN))) -> (write('Sicstus: Innapropriate call to API'), fail) ; true),
        sicstus_alldiff_list(LEN, GRAIN, RES, -2147483648, 2147483647). % signed 32 bits - -2**31..2**31-1
sicstus_alldiff_list(LEN, GRAIN, RES, Min, Max) :-
        (\+((integer(LEN),var(RES), integer(GRAIN), integer(Min), integer(Max), Min =< Max)) -> (write('Sicstus: Innapropriate call to API'), fail) ; true),
        lists:length(L, LEN),
        Max1 is Max+1,
        setrand(GRAIN),
        mutdict:new_mutdict(DICT),
        random_gen(L, DICT, Min, Max1),
        mutdict:mutdict_size(DICT, LEND),
        complement_unsorted(DICT, LEND, LEN, Min, Max1, 1000, RES).   % Max 1000 attempts to complement the list

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% UTILS
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
random_gen([], _Min, _Max) :-!.
random_gen([X|Xs], Min, Max) :-
        random:random(Min, Max, X),
        random_gen(Xs, Min, Max).

random_gen([], _DICT, _Min, _Max) :- !.
random_gen([X|Xs], DICT, Min, Max) :-
        random:random(Min, Max, X),
        ( mutdict:mutdict_get(DICT, X,  X) -> true ; mutdict:mutdict_put(DICT, X, X)),
        random_gen(Xs, DICT, Min, Max).

% Without mutdict
%random_gen([], LDIFF, LDIFF, _Min, _Max) :- !.
%random_gen([X|Xs], LDIFF1, LDIFF3, Min, Max) :-
%        random:random(Min, Max, X),
%%         ( lists:nth1(_, LDIFF1, X) -> LDIFF2 = LDIFF1 ; LDIFF2 = [X|LDIFF1]),
% %        ( lists:nth0(_, LDIFF1, X) -> LDIFF2 = LDIFF1 ; LDIFF2 = [X|LDIFF1]),
%        ( lists:select(X, LDIFF1, _) -> LDIFF2 = LDIFF1 ; LDIFF2 = [X|LDIFF1]),
%        random_gen(Xs, LDIFF2, LDIFF3, Min, Max).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Attempt to boost the generator "sans remise", using random_select - Unfruitful
%
%
%random_gen1(L, Min, Max, LI_END):-
%        between:numlist(Min, Max, LI),
%        random_gen_in(L, LI, LI_END).
%
%random_gen_in([], LI, LI) :- !.
%random_gen_in([X|Xs], LI, LI_END) :-
%        random:random_select(X, LI, LI_NEXT),
%        random_gen_in(Xs, LI_NEXT, LI_END).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

add_random(0, _N, _DICT, _Min, _Max):-!.
add_random(_M, 0, _DICT, _Min, _Max):-!.
add_random(M, N, DICT, Min, Max):-
         random:random(Min, Max, X),
                                %         ( lists:nth1(_, LDIFF1, X) -> (N1 = N, LDIFF2=LDIFF1) ; (N1 is N-1, LDIFF2 = [X|LDIFF1])),
          ( mutdict:mutdict_get(DICT, X,  X) -> N1 = N ; (N1 is N-1, mutdict:mutdict_put(DICT, X, X)) ),
         M1 is M-1,
         add_random(M1, N1, DICT, Min, Max).

complement_sorted(DICT, LEND, LEN, Min, Max, M, RES) :-
        LEND < LEN, !,
        DIFF is LEN - LEND,
        add_random(M, DIFF, DICT,  Min, Max),
        mutdict:mutdict_values(DICT, LDIFF),
        sort(LDIFF, RES).
complement_sorted(DICT, _LEND, _LEN, _Min, _Max, _M,  RES):-
        mutdict:mutdict_values(DICT, LDIFF),
        sort(LDIFF, RES).

complement_unsorted(DICT, LEND, LEN, Min, Max, M, RES) :-
        LEND < LEN, !,
        DIFF is LEN - LEND,
        add_random(M, DIFF, DICT, Min, Max),
        mutdict:mutdict_values(DICT, RES).
complement_unsorted(DICT, _LEND, _LEN, _Min, _Max, _M,  RES):-
        mutdict:mutdict_values(DICT, RES).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% random labelling
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

                                % Labeling to find K diverse incumbents which maximize a given variable Z
                                % Beware: It does not compute all solutions of the csp, only the last incumbents
                                % Predicate: label/4, label/5
                                % OPTIONS:
                                % time(T): Time_out in seconds
                                % var(left): select leftmost var | var(random): select var at random
                                % random_val(value) | random_val(split)
                                % dist(h) | dist(l1) | dist(l2)


                                % ?- VARS = [X1, X2, X3, X4, X5], csp2(VARS, SUM), label(VARS, SUM, _K, Incum, [time(1)]).
                                % ?- VARS = [X1, X2, X3, X4, X5], csp2(VARS, SUM), label(VARS, SUM, 3, Incum, [time(1), random_val(value)]).
                                % ?- VARS = [X1, X2, X3, X4, X5], csp2(VARS, SUM), label(VARS, SUM, 4, Incum, [var(random), time(1)]).
                                % ?- length(_VARS, 100), csp3(_VARS, SUM), label(_VARS, SUM, 20, Incum, [random_val(split), var(left), time(1)]).


label(VARS, Z, K, Incumbents):-
        label(VARS, Z, K, Incumbents, []).
label(VARS, Z, K, Incumbents, OPTIONS):-
        treat_options(OPTIONS, OPTS1, OPTS2),
        findall(VARS, labeling([maximize(Z), all, restart|OPTS1], VARS), Solutions),
        length(Solutions, M),
        ( (nonvar(K), K < M) ->  myKlast(M, Solutions, K, Incumbents, OPTS2) ; Incumbents = Solutions).

treat_options([], [], []).
treat_options(OPTIONS, [time_out(T1, _Flag)|OPTS1], OPTS2):-
        select(time(T), OPTIONS, R_OPTIONS),
        !,
        T1 is 1000 * T,
        treat_options(R_OPTIONS, OPTS1, OPTS2).
treat_options(OPTIONS, [variable(select_var(O))|OPTS1], OPTS2):-
        select(var(O), OPTIONS, R_OPTIONS),
        !,
        treat_options(R_OPTIONS, OPTS1, OPTS2).
treat_options(OPTIONS, [value(random_val(O))|OPTS1], OPTS2):-
        select(random_val(O), OPTIONS, R_OPTIONS),
        !,
        treat_options(R_OPTIONS, OPTS1, OPTS2).
treat_options(OPTIONS, OPTS1, [dist(DIST)|OPTS2]):-
        select(dist(DIST), OPTIONS, R_OPTIONS),
        !,
        treat_options(R_OPTIONS, OPTS1, OPTS2).

select_var(_OPT, [X], X, []) :- !.
select_var(left, [X|L], X, L).
select_var(random, L, Sel, Rest) :-
        random:random_select(Sel, L, Rest).

random_val(value,  X,  _Rest,  BB0,  BB) :-
        fd_min(X, Min), fd_max(X, Max),
        Max1 is Max+1,
        random(Min, Max1, R),
        ( X #= R, first_bound(BB0, BB)  ; X #\= R, later_bound(BB0, BB) ).

random_val(split,  X,  _Rest,  BB0,  BB) :-
        fd_min(X, Min), fd_max(X, Max),
        Max1 is Max+1,
        random(Min, Max1, R),
        ( X #= R, first_bound(BB0, BB)  ; X #<R, later_bound(BB0, BB) ; X #> R, later_bound(BB0, BB) ).


% Two main predicates with the following parameters
%    Seq is a sequence of uniform random vectors for VARS, satisfying C a set of constraints
%    N is the expected length of Seq -
%    K is the division parameter
%
%   rt  : "pure" random testing implementation
%   prt : our path-oriented random implementation

% Warning: constraints are posted to clpfd

% Examples:
%   ?- rt(domain([X,Y],0,100), (Y #> X + 50, X*Y #< 60), [X,Y], 1000, Seq1).
%   ?- prt((domain([X,Y],0,100), Y #> X + 50, X*Y #< 60), [X,Y], 1000, 2, Seq3).

%%% ?- sorting([X1, X2, X3], [P1, P2, P3], [Y1, Y2, Y3]), X1 = 5.
%%% ?- keysorting([[X1], [X2], [X3]], [[Y1], [Y2], [Y3]]).
%%% ?-  keysorting([[X1], [X2], [X3]], [[Y1], [Y2], [Y3]]), X1 in 0..5, X2 in 2..7, X3 in 6..10.

%%% ?- L1 = [X1, X2, X3], L2 = [Y1, Y2, Y3], domain(L1, 0, 10), domain(L2, 0, 10), keysorting([[X1], [X2], [X3]], [[Y1], [Y2], [Y3]], [permutation([P1, P2, P3])]), Y1 = 3, X1 = 5, X2 = 4.

%%%  ?- rt((L1 = [X1, X2, X3], L2 = [Y1, Y2, Y3], domain(L1, 0, 29), domain(L2, 0, 29)), (keysorting([[X1], [X2], [X3]], [[Y1], [Y2], [Y3]])), [X1, X2, X3, Y1, Y2, Y3], 100, Seq).

%%% ?- prt((L1 = [X1, X2, X3], L2 = [Y1, Y2, Y3], domain(L1, 0, 29), domain(L2, 0, 29), keysorting([[X1], [X2], [X3]], [[Y1], [Y2], [Y3]])), [X1, X2, X3, Y1, Y2, Y3], 100, 2, Seq).
%%% ?- prt((L1 = [X1, X2, X3], L2 = [Y1, Y2, Y3], domain(L1, 0, 29), domain(L2, 0, 29), keysorting([[X1], [X2], [X3]], [[Y1], [Y2], [Y3]])), [X1, X2, X3, Y1, Y2, Y3], 100, 3, Seq).
%%% ?- prt((L1 = [X1, X2, X3], L2 = [Y1, Y2, Y3], domain(L1, 0, 29), domain(L2, 0, 29), keysorting([[X1], [X2], [X3]], [[Y1], [Y2], [Y3]])), [X1, X2, X3, Y1, Y2, Y3], 100, 4, Seq).

%%% ?- prt((L1 = [X1, X2, X3], L2 = [Y1, Y2, Y3], domain(L1, 0, 5), domain(L2, 0, 5), keysorting([[X1], [X2], [X3]], [[Y1], [Y2], [Y3]], [permutation([P1, P2, P3])])), [X1, X2, X3, Y1, Y2, Y3], 100, 2, Seq).

prt(N, K, Seq) :-
        C = (domain([X,Y],0,100), Y #> X + 50, X*Y #< 60),
        V = [X, Y],
        write(' -- Prolog Command -- '), write('prt('),write(N), write(','), write(K), write(','), write(Seq), write(')'),nl,
        prt(C, V, N, K, Seq).
%        write(Seq), nl.

prt(C, VARS, N, K, Seq) :-
        write(' -- Prolog Command -- '), write('prt('),write(C), write(','), write(VARS), write(','), write(N), write(','), write(K), write(','), write(Seq), write(')'),nl,
        call(C),
        divide(VARS,K, DOMS),  % divide the domain of each var in VARS in K subdomains
        build_cartesian_product(DOMS, CP_DOMS),  % complexity = K^#VARS
        reverse(VARS,RVARS),
        inconsistency_check(RVARS, CP_DOMS, TRUE_DOMS, LEN, NB_INCONS),  % remove inconstant domains
        M is 3*N,
        random_choice_dom(M, LEN, TRUE_DOMS, N_TRUE_DOMS, F), % build a seq of randomly choosed domain
        F = N_TRUE_DOMS,  % N_TRUE_DOMS becomes an endless lists
        iterate_N(N, N_TRUE_DOMS, RVARS, Seq, NB),  % generate Seq
        ((number(LEN),number(NB_INCONS)) -> NB_DOM is LEN + NB_INCONS ; true ),
        write('nb of inconsistant domains: '), write(NB_INCONS), write(' over a total of '), write(NB_DOM), write(' domains'),
        nl,
        write('length of the random sequence generated: '), write(NB),
        nl.

iterate_N(0, _DOMS, _VARS, [], 0):-!.
iterate_N(N, [D|DOMS], VARS, [X|S], NB) :-
        \+( \+( (random_choice_val(D, VARS),reverse(VARS,RVARS), assert(t(RVARS)) ) ) ),  % may fail due to an inconsistant choice
        !,
        retract(t(X)),
        N1 is N-1,
        iterate_N(N1, DOMS, VARS, S, NB1),
        NB is NB1 + 1.
iterate_N(N, [_D|DOMS], VARS, S, NB) :-
        iterate_N(N, DOMS, VARS, S, NB1),
        NB is NB1 + 1.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% divide(VARS, K, D)
% D is a list of K domains of the same size
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
divide([],_K,[]):-!.
divide([X|S], K, [D|SD]) :-
        fd_min(X, Min),
        fd_max(X, Max),
        Size is Max - Min - 1,
        Rem is Size mod K,
        Pas is (Max - Min + Rem) // K,
        build(K, Pas, Min, _NMax, D),
        divide(S, K, SD).

build(0, _Pas, NMax, NMax, []):-!.
build(K, Pas, Min, NMax, [[Min,M]|S]):-
        M is Min+Pas,
        M1 is M+1,
        K1 is K-1,
        build(K1,Pas, M1, NMax, S).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% build_cartesian_product(DOMS, CP_DOMS)
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
build_cartesian_product([D], D) :- !.
build_cartesian_product([L1,L2], D) :-
        !,
        list_to_ord_set(L1,D1),   % optional
        list_to_ord_set(L2,D2),   % optional
        ord_setproduct(D1,D2, D).
build_cartesian_product([L1,L2|S], RES) :-
        build_cartesian_product([L1,L2], D),
        build_cartesian_product([D|S], RES).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% inconsistency_check(DOMS_K, TRUE_DOMS, LK)
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
inconsistency_check(_VARS, [], [], 0, 0):-!.
inconsistency_check(VARS, [DOM|DOMS], TRUE_DOMS, LEN, NB) :-
        \+( assign_fd(VARS, DOM) ),
        !,
        inconsistency_check(VARS, DOMS, TRUE_DOMS, LEN, NB1),
        NB is NB1+1.
inconsistency_check(VARS, [DOM|DOMS], [DOM|TRUE_DOMS], LEN, NB) :-
        inconsistency_check(VARS, DOMS, TRUE_DOMS, LEN1, NB),
        LEN is LEN1+1.


assign_fd([X],[Min,Max]) :-
        X in Min .. Max,
        !.
assign_fd([X|S], DS-[Min,Max]) :-
        X in Min .. Max,
        assign_fd(S,DS).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% random_choice_dom(N, LEN, TRUE_DOMS, N_TRUE_DOMS)
% random_choice_val(D,X)
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
random_choice_dom(0, _LEN, _TRUE_DOMS, F,F) :- !.
random_choice_dom(N, LEN, TRUE_DOMS, [TD|N_TRUE_DOMS],F) :-
        N1 is N-1,
        LEN1 is LEN+1,
        random(1,LEN1,R),
%        lists:nth1(R, TRUE_DOMS, TD),  % SICSTUS 4
        lists:nth1(R, TRUE_DOMS, TD),    % SICSTUS 3
        random_choice_dom(N1, LEN, TRUE_DOMS, N_TRUE_DOMS,F).

random_choice_val([M,M], [X]) :-
        X = M,
        !.
random_choice_val([Min,Max], [X]) :-
        Max1 is Max+1,
        random(Min, Max1, R),
        X = R,
        !.
random_choice_val(D2-[M,M], [X|S1]) :-
        X = M,
        !,
        random_choice_val(D2,S1).
random_choice_val(D2-[Min,Max], [X|S1]) :-
        Max1 is Max+1,
        random(Min, Max1, R),
        X = R,
        !,
        random_choice_val(D2, S1).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% RT without constraint propagation
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
rt(DOM, C, VARS, N, Seq) :-
        call(DOM),
        random_rt(N,5000000, VARS, C, Seq, NB),
        write('length of the random sequence generated: '), write(NB),
        nl.

random_rt(_N,0, _VARS, _C, _Seq, 5000000) :-!.
random_rt(0,_M, _VARS, _C, [], 0) :-!.

random_rt(N, M, VARS, C, LISTE, NB) :-
        \+( \+( (rrt_rec(VARS, C, V), assert((f(V)))) ) ),
        !,
        retract(f(V)),
        N1 is N-1,
        random_rt(N1, M, VARS, C, S, NB1),
        NB is NB1 + 1,
        LISTE = [V|S].
random_rt(N,M, VARS, C, S,NB) :-
        M1 is M-1,
        random_rt(N,M1,VARS, C, S, NB1),
        NB is NB1 + 1.

rrt_rec([], C, []) :-
        call(C),
        !.
rrt_rec([X|Xs], C, [V|Vs]) :-
        fd_min(X, Min),
        fd_max(X, Max),
        Max1 is Max+1,
        random(Min, Max1, V),
        X #= V,
        rrt_rec(Xs, C, Vs).
