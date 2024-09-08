:- module(rcpearl, [
              path//1,
              state_tallies/2
          ]).

:- use_module(library(lists)).
:- use_module(library(clpz)).
:- use_module(library(reif)).
:- use_module(library(dcgs)).
:- use_module(library(error)).
:- use_module(library(si)).
:- use_module(library(lambda)).
% TODO: Consider moving these declarations to separate unit-testing files.
:- use_module(library(pairs)).
:- use_module(library(time)).
:- use_module(library(format)).
:- use_module(library(debug)).
:- use_module(library(assoc)). % Only for exploring recursion relations
:- initialization(assertz(clpz:monotonic)).
allowed_cohort_sizes([3]).
valid_tally(T/N) :- valid_denom(N), 0 #=< #T, #T #=< N.
valid_denom(N) :- N in 0..6.
enroll(T0/N0, T/N) :-
    allowed_cohort_sizes(Cs),
    member(Nnew, Cs),
    #N #= #N0 + #Nnew,
    valid_denom(N),
    Tnew in 0..Nnew, indomain(Tnew),
    #T #= #T0 + #Tnew.
valid_state(Ls - Hs) :-
    append(Ls, Hs, Ds),
    length(Ds, ND), ND in 1..8,
    maplist(valid_tally, Ds).

state_tallies(Ls-Hs, Qs) :-
    valid_state(Ls-Hs),
    reverse(Ls, Js),
    append(Js, Hs, Qs).
state0_decision_state(Ls - [H0|Hs], esc, [H|Ls] - Hs) :-
    valid_state(Ls - [H0|Hs]),
    enroll(H0, H).
state0_decision_state([L0|Ls] - Hs, sta, [L|Ls] - Hs) :- 
    valid_state([L0|Ls] - Hs),
    enroll(L0, L).
state0_decision_state([L,D0|Ls] - Hs, des, [D|Ls] - [L|Hs]) :- 
    valid_state([L,D0|Ls] - Hs),
    enroll(D0, D).
state0_decision_infeasible_t(_-[], esc, true).
state0_decision_infeasible_t([_]-_, des, true).
state0_decision_infeasible_t(_-[_/N|_], esc, true)   :- #N #>= 6.
state0_decision_infeasible_t([_/N|_]-_, sta, true)   :- #N #>= 6.
state0_decision_infeasible_t([_,_/N|_]-_, des, true) :- #N #>= 6.
state0_decision_infeasible_t(S0, E, false) :-
    member(E, [esc,sta,des]),
    Goal = exists_subsequent_state(S0, E),
    once((term_si(Goal), Goal)).

exists_subsequent_state(S0, E) :-
    state0_decision_state(S0, E, _).
enroll_tallies(C, Qs) :-
    n_countdown(C, Ts),
    maplist(\T^(=(T/C)), Ts, Qs).

n_countdown(N, [N|Ns]) :- #N #> 0, #Nminus1 #= N - 1,
                          n_countdown(Nminus1, Ns).
n_countdown(0, [0]).
enrollments_tallies([C|Cs], Qs) :-
    enroll_tallies(C, Q0s),
    append(Q0s, Q1s, Qs),
    enrollments_tallies(Cs, Q1s).
enrollments_tallies([], []).
tally0_tallies(T0/N0, Tallies) :-
    valid_tally(T0/N0),
    allowed_cohort_sizes(Cs),
    enrollments_tallies(Cs, Qs),
    maplist(\Qnew^Q^(Qnew=Tnew/Nnew,
                     #T #= T0 + Tnew,
                     #N #= N0 + Nnew, Q=T/N),
            Qs, Tallies).
state0_decision_histories(S0, E, Hs) :-
    (   E = esc,
        S0 = [T0/N0|_] - [Told/Nold|_]
    ;   E = sta,
        S0 = [T0/N0|_] - _,
        Told = T0, Nold = N0
    ;   E = des,
        S0 = [T0/N0, Told/Nold | _] - _
    ),
    tally0_tallies(Told/Nold, Qs),
    maplist(\Q^(=([Q, T0/N0])), Qs, Hs).
decision_q0_q_regret(esc, T0/N0, _, #\ ( #N0 #>= 3 #/\ #T0 * 6 #=< N0 )).
decision_q0_q_regret(des, T0/N0, T/N,
                     ( #T0 #=< 1 #/\ #N0 #>= 3 ) #/\
                     ( #N #> 0 #/\ #T * 6 #< #N )
                    ).
decision_q0_q_regret(esc, _, T/_, #T #>= 5).
decision_q0_q_regret(sta, _, T/_, #T #>= 5).
decision_q0_q_regret(des, _, T/_, #T #>= 5).
% Generate e_vars_disjunction _at compile time_.
:- dynamic(e_vars_disjunction/3).
term_expansion(generate_clauses, Clauses) :-
    findall(e_vars_disjunction(E, Vars, Disjunction),
            (   member(E, [esc,sta,des]),
                findall(Vs-RC,
                        (   decision_q0_q_regret(E, T0/N0, T/N, RC),
                            Vs = [N0,N,T0,T]
                        ), VsRCs),
                pairs_keys_values(VsRCs, Vs, RCs),
                maplist(=(Vars), Vs),
                foldl(\X^Disj0^Disj^(Disj=(Disj0#\/X)), RCs, 0#=1, Disjunction)
            ),
            Clauses).
generate_clauses.

regret_t(E, H, Truth)  :-
    e_h_disjunction(E, H, Disjunction),
    Disjunction #<==> #B,
    b_t(B, Truth).

b_t(0, false).
b_t(1, true).

e_h_disjunction(E, H, Disjunction) :-
    H = [T/N, T0/N0],
    e_vars_disjunction(E, [N0,N,T0,T], Disjunction).
/*
?- listing(e_vars_disjunction/3).
 e_vars_disjunction(esc,[A,B,C,D],0#=1#\/ #\ (#A#>=3#/\ #C*6#=<A)#\/ #D#>=5).
 e_vars_disjunction(sta,[A,B,C,D],0#=1#\/ #D#>=5).
 e_vars_disjunction(des,[A,B,C,D],
                  0#=1#\/ #C#=<1#/\ #A#>=3#/\(#B#>0#/\ #D*6#< #B)#\/ #D#>=5).
    true.
*/
state0_decision_regrets(S0, E, Regrets) :- 
    state0_decision_histories(S0, E, Hs),
    tfilter(regret_t(E), Hs, Regrets).
state0_decision_regrettable_t(S0, E, false) :- 
    state0_decision_regrets(S0, E, []).
state0_decision_regrettable_t(S0, E, true) :- 
    state0_decision_regrets(S0, E, [_|_]).
state0_nextdecision(S0, E) :-
    if_((   state0_decision_infeasible_t(S0, esc)
        ;   state0_decision_regrettable_t(S0, esc)),
        if_((   state0_decision_infeasible_t(S0, sta)
            ;   state0_decision_regrettable_t(S0, sta)),
            if_((   state0_decision_infeasible_t(S0, des)
                ;   state0_decision_regrettable_t(S0, des)),
                E = stop,
                E = des),
            E = sta),
        E = esc).
path(S0) --> { state0_nextdecision(S0, E),
               state0_decision_state(S0, E, S) },
             [E, S],
             path(S).
path(S0) --> { state0_nextdecision(S0, stop),
               stopstate_rec(S0, Rec) },
             [stop, recommend_dose(Rec)].
path(recommend_dose(_)) --> [].
stopstate_rec([]-_, 0).
stopstate_rec([T/N|TNs]-_, Rec) :- 
        (   #T * 6 #> #N, length(TNs, Rec)
        ;   #T * 6 #=< #N, length([_|TNs], Rec)
        ).
/*
?- setof(E^S1, Etc^(phrase(path([0/0]-[0/0,0/0]), [E, S1 | Etc])),
         Starts).
   Starts = [sta^([0/3]-[0/0,0/0]),sta^([1/3]-[0/0,0/0]),
             sta^([2/3]-[0/0,0/0]),sta^([3/3]-[0/0,0/0])].
*/
/*
?- setof(E, Path^Ls^H^Hs^(phrase(path([0/0]-[0/0,0/0]), Path),
             phrase((..., [[0/3|Ls]-[H|Hs]], [E], ...), Path)), Es).
   Es = [esc].
*/
/*
?- setof(E, Path^Ls^H^Hs^(phrase(path([0/0]-[0/0,0/0]), Path),
             phrase((..., [[1/3|Ls]-[H|Hs]], [E], ...), Path)), Es).
   Es = [sta].
*/
/*
?- setof(E, Path^Ls^H^Hs^(phrase(path([0/0]-[0/0,0/0]), Path),
                          %%H = 0/0,
                phrase((...,[[1/6|Ls]-[H|Hs]],[E],...), Path)), Es).
%@    Es = [esc,stop].
%@    Es = [esc].
   Es = [esc].
*/
recommends_dose_exceeding_mtd             :- 
   D in 1..8, indomain(D),       % For trials of up to D=8 doses
   InitD = [Q]-Qs, length([Q|Qs], D), % .. that start from the lowest dose
   maplist(=(0/0), [Q|Qs]),      % .. with no prior toxicity information,
   phrase(path(InitD), Path),    % does any Path exist
   phrase((..., [Ls-_], ...,     % .. on which a state Ls-_ appears,
           [recommend_dose(Rec)] % .. such that the recommended dose Rec
          ), Path),
   length(Ls,X), Rec #>= X,      % .. was at least the current dose X,
   Ls = [T/_|_], #T #> 1.        % .. yet X `exceeded MTD' per protocol?
%?- time(recommends_dose_exceeding_mtd).
%@    % CPU time: 574.029s, 2_701_969_903 inferences
%@    false.
%@    % CPU time: 721.342s, 3_070_516_127 inferences
%@    false. % This safety property is verified for trials of up to 8 doses.
trial_fails_to_conclude_with_unique_rec :-
   D in 1..8, indomain(D), length([Q|Qs], D), maplist(=(0/0), [Q|Qs]),
   phrase(path([Q]-Qs), Path),
   (   phrase((..., [recommend_dose(Rec)], [_], ...), Path)
   ;   \+ phrase((..., [recommend_dose(Rec)]), Path)
   ).
%?- time(trial_fails_to_conclude_with_unique_rec).
%@    % CPU time: 560.946s, 2_675_988_416 inferences
%@    false.
%@    % CPU time: 736.051s, 3_044_534_640 inferences
%@    false. % All trials of up to 8 doses yield a recommendation, then stop.
/*
?- setof(E, Path^(phrase(path([0/0]-[0/0,0/0]), Path),
                  phrase((...,[[0/3,0/3,0/3]-[], E], ...), Path)), Es).
   Es = [sta].
*/
/*
?- setof(E0, Path^(phrase(path([0/0]-[0/0,0/0]), Path),
                   phrase((...,[E0, [0/3,0/3,0/3]-[]],...), Path)), E0s).
   E0s = [esc].
*/
/*
?- setof(Rec, Path^(phrase(path([0/0]-[0/0,0/0]), Path),
                    phrase((..., [[2/6,0/3,0/3]-[]],
                            ..., [recommend_dose(Rec)]), Path)), Recs).
   Recs = [0,1,2]. % Only dose level 3 has been ruled out so far.
*/
/*
?- J+\time((D = 8, length([Q|Qs], D), maplist(=(0/0), [Q|Qs]),
            setof(Path, phrase(path([Q]-Qs), Path), Paths),
            length(Paths, J))).
%@    % CPU time: 337.638s, 1_573_175_565 inferences
%@    J = 16138.
%@    % CPU time: 415.023s, 1_799_146_944 inferences
%@    J = 16138.
*/
% Uncomment to allow 'rolling enrollment':
%%allowed_cohort_sizes([3,2,1]).
/*
?- phrase(path([0/3,0/3,0/3]-[]), [sta, [2/5,0/3,0/3]-[],
                                   des, [0/6,0/3]-[2/5],
                                   stop, recommend_dose(2)]).
%@    true
%@ ;  ... .
   true % The above-described path is admissible.
;  ... .
*/
/*
:- use_module(library(format)).
?- J+\(setof(Path, (phrase(path([0/0]-[0/0]), Path)), Paths)
      , maplist(portray_clause, Paths), length(Paths, J)).
%@ [sta,[0/3]-[0/0],esc,[0/3,0/3]-[],sta,[0/6,0/3]-[],stop,recommend_dose(2)].
%@ [sta,[0/3]-[0/0],esc,[0/3,0/3]-[],sta,[1/6,0/3]-[],stop,recommend_dose(2)].
%@ [sta,[0/3]-[0/0],esc,[0/3,0/3]-[],sta,[2/6,0/3]-[],des,[0/6]-[2/6],stop,recommend_dose(1)].
%@ [sta,[0/3]-[0/0],esc,[0/3,0/3]-[],sta,[2/6,0/3]-[],des,[1/6]-[2/6],stop,recommend_dose(1)].
%@ [sta,[0/3]-[0/0],esc,[0/3,0/3]-[],sta,[2/6,0/3]-[],des,[2/6]-[2/6],stop,recommend_dose(0)].
%@ [sta,[0/3]-[0/0],esc,[0/3,0/3]-[],sta,[2/6,0/3]-[],des,[3/6]-[2/6],stop,recommend_dose(0)].
%@ [sta,[0/3]-[0/0],esc,[0/3,0/3]-[],sta,[3/6,0/3]-[],des,[0/6]-[3/6],stop,recommend_dose(1)].
%@ [sta,[0/3]-[0/0],esc,[0/3,0/3]-[],sta,[3/6,0/3]-[],des,[1/6]-[3/6],stop,recommend_dose(1)].
%@ [sta,[0/3]-[0/0],esc,[0/3,0/3]-[],sta,[3/6,0/3]-[],des,[2/6]-[3/6],stop,recommend_dose(0)].
%@ [sta,[0/3]-[0/0],esc,[0/3,0/3]-[],sta,[3/6,0/3]-[],des,[3/6]-[3/6],stop,recommend_dose(0)].
%@ [sta,[0/3]-[0/0],esc,[1/3,0/3]-[],sta,[1/6,0/3]-[],stop,recommend_dose(2)].
%@ [sta,[0/3]-[0/0],esc,[1/3,0/3]-[],sta,[2/6,0/3]-[],des,[0/6]-[2/6],stop,recommend_dose(1)].
%@ [sta,[0/3]-[0/0],esc,[1/3,0/3]-[],sta,[2/6,0/3]-[],des,[1/6]-[2/6],stop,recommend_dose(1)].
%@ [sta,[0/3]-[0/0],esc,[1/3,0/3]-[],sta,[2/6,0/3]-[],des,[2/6]-[2/6],stop,recommend_dose(0)].
%@ [sta,[0/3]-[0/0],esc,[1/3,0/3]-[],sta,[2/6,0/3]-[],des,[3/6]-[2/6],stop,recommend_dose(0)].
%@ [sta,[0/3]-[0/0],esc,[1/3,0/3]-[],sta,[3/6,0/3]-[],des,[0/6]-[3/6],stop,recommend_dose(1)].
%@ [sta,[0/3]-[0/0],esc,[1/3,0/3]-[],sta,[3/6,0/3]-[],des,[1/6]-[3/6],stop,recommend_dose(1)].
%@ [sta,[0/3]-[0/0],esc,[1/3,0/3]-[],sta,[3/6,0/3]-[],des,[2/6]-[3/6],stop,recommend_dose(0)].
%@ [sta,[0/3]-[0/0],esc,[1/3,0/3]-[],sta,[3/6,0/3]-[],des,[3/6]-[3/6],stop,recommend_dose(0)].
%@ [sta,[0/3]-[0/0],esc,[1/3,0/3]-[],sta,[4/6,0/3]-[],des,[0/6]-[4/6],stop,recommend_dose(1)].
%@ [sta,[0/3]-[0/0],esc,[1/3,0/3]-[],sta,[4/6,0/3]-[],des,[1/6]-[4/6],stop,recommend_dose(1)].
%@ [sta,[0/3]-[0/0],esc,[1/3,0/3]-[],sta,[4/6,0/3]-[],des,[2/6]-[4/6],stop,recommend_dose(0)].
%@ [sta,[0/3]-[0/0],esc,[1/3,0/3]-[],sta,[4/6,0/3]-[],des,[3/6]-[4/6],stop,recommend_dose(0)].
%@ [sta,[0/3]-[0/0],esc,[2/3,0/3]-[],des,[0/6]-[2/3],stop,recommend_dose(1)].
%@ [sta,[0/3]-[0/0],esc,[2/3,0/3]-[],des,[1/6]-[2/3],stop,recommend_dose(1)].
%@ [sta,[0/3]-[0/0],esc,[2/3,0/3]-[],des,[2/6]-[2/3],stop,recommend_dose(0)].
%@ [sta,[0/3]-[0/0],esc,[2/3,0/3]-[],des,[3/6]-[2/3],stop,recommend_dose(0)].
%@ [sta,[0/3]-[0/0],esc,[3/3,0/3]-[],des,[0/6]-[3/3],stop,recommend_dose(1)].
%@ [sta,[0/3]-[0/0],esc,[3/3,0/3]-[],des,[1/6]-[3/3],stop,recommend_dose(1)].
%@ [sta,[0/3]-[0/0],esc,[3/3,0/3]-[],des,[2/6]-[3/3],stop,recommend_dose(0)].
%@ [sta,[0/3]-[0/0],esc,[3/3,0/3]-[],des,[3/6]-[3/3],stop,recommend_dose(0)].
%@ [sta,[1/3]-[0/0],sta,[1/6]-[0/0],esc,[0/3,1/6]-[],sta,[0/6,1/6]-[],stop,recommend_dose(2)].
%@ [sta,[1/3]-[0/0],sta,[1/6]-[0/0],esc,[0/3,1/6]-[],sta,[1/6,1/6]-[],stop,recommend_dose(2)].
%@ [sta,[1/3]-[0/0],sta,[1/6]-[0/0],esc,[0/3,1/6]-[],sta,[2/6,1/6]-[],stop,recommend_dose(1)].
%@ [sta,[1/3]-[0/0],sta,[1/6]-[0/0],esc,[0/3,1/6]-[],sta,[3/6,1/6]-[],stop,recommend_dose(1)].
%@ [sta,[1/3]-[0/0],sta,[1/6]-[0/0],esc,[1/3,1/6]-[],sta,[1/6,1/6]-[],stop,recommend_dose(2)].
%@ [sta,[1/3]-[0/0],sta,[1/6]-[0/0],esc,[1/3,1/6]-[],sta,[2/6,1/6]-[],stop,recommend_dose(1)].
%@ [sta,[1/3]-[0/0],sta,[1/6]-[0/0],esc,[1/3,1/6]-[],sta,[3/6,1/6]-[],stop,recommend_dose(1)].
%@ [sta,[1/3]-[0/0],sta,[1/6]-[0/0],esc,[1/3,1/6]-[],sta,[4/6,1/6]-[],stop,recommend_dose(1)].
%@ [sta,[1/3]-[0/0],sta,[1/6]-[0/0],esc,[2/3,1/6]-[],stop,recommend_dose(1)].
%@ [sta,[1/3]-[0/0],sta,[1/6]-[0/0],esc,[3/3,1/6]-[],stop,recommend_dose(1)].
%@ [sta,[1/3]-[0/0],sta,[2/6]-[0/0],stop,recommend_dose(0)].
%@ [sta,[1/3]-[0/0],sta,[3/6]-[0/0],stop,recommend_dose(0)].
%@ [sta,[1/3]-[0/0],sta,[4/6]-[0/0],stop,recommend_dose(0)].
%@ [sta,[2/3]-[0/0],stop,recommend_dose(0)].
%@ [sta,[3/3]-[0/0],stop,recommend_dose(0)].
%@    J = 46.
[sta,[0/3]-[0/0],esc,[0/3,0/3]-[],sta,[0/6,0/3]-[],stop,recommend_dose(2)].
[sta,[0/3]-[0/0],esc,[0/3,0/3]-[],sta,[1/6,0/3]-[],stop,recommend_dose(2)].
[sta,[0/3]-[0/0],esc,[0/3,0/3]-[],sta,[2/6,0/3]-[],des,[0/6]-[2/6],stop,recommend_dose(1)].
[sta,[0/3]-[0/0],esc,[0/3,0/3]-[],sta,[2/6,0/3]-[],des,[1/6]-[2/6],stop,recommend_dose(1)].
[sta,[0/3]-[0/0],esc,[0/3,0/3]-[],sta,[2/6,0/3]-[],des,[2/6]-[2/6],stop,recommend_dose(0)].
[sta,[0/3]-[0/0],esc,[0/3,0/3]-[],sta,[2/6,0/3]-[],des,[3/6]-[2/6],stop,recommend_dose(0)].
[sta,[0/3]-[0/0],esc,[0/3,0/3]-[],sta,[3/6,0/3]-[],des,[0/6]-[3/6],stop,recommend_dose(1)].
[sta,[0/3]-[0/0],esc,[0/3,0/3]-[],sta,[3/6,0/3]-[],des,[1/6]-[3/6],stop,recommend_dose(1)].
[sta,[0/3]-[0/0],esc,[0/3,0/3]-[],sta,[3/6,0/3]-[],des,[2/6]-[3/6],stop,recommend_dose(0)].
[sta,[0/3]-[0/0],esc,[0/3,0/3]-[],sta,[3/6,0/3]-[],des,[3/6]-[3/6],stop,recommend_dose(0)].
[sta,[0/3]-[0/0],esc,[1/3,0/3]-[],sta,[1/6,0/3]-[],stop,recommend_dose(2)].
[sta,[0/3]-[0/0],esc,[1/3,0/3]-[],sta,[2/6,0/3]-[],des,[0/6]-[2/6],stop,recommend_dose(1)].
[sta,[0/3]-[0/0],esc,[1/3,0/3]-[],sta,[2/6,0/3]-[],des,[1/6]-[2/6],stop,recommend_dose(1)].
[sta,[0/3]-[0/0],esc,[1/3,0/3]-[],sta,[2/6,0/3]-[],des,[2/6]-[2/6],stop,recommend_dose(0)].
[sta,[0/3]-[0/0],esc,[1/3,0/3]-[],sta,[2/6,0/3]-[],des,[3/6]-[2/6],stop,recommend_dose(0)].
[sta,[0/3]-[0/0],esc,[1/3,0/3]-[],sta,[3/6,0/3]-[],des,[0/6]-[3/6],stop,recommend_dose(1)].
[sta,[0/3]-[0/0],esc,[1/3,0/3]-[],sta,[3/6,0/3]-[],des,[1/6]-[3/6],stop,recommend_dose(1)].
[sta,[0/3]-[0/0],esc,[1/3,0/3]-[],sta,[3/6,0/3]-[],des,[2/6]-[3/6],stop,recommend_dose(0)].
[sta,[0/3]-[0/0],esc,[1/3,0/3]-[],sta,[3/6,0/3]-[],des,[3/6]-[3/6],stop,recommend_dose(0)].
[sta,[0/3]-[0/0],esc,[1/3,0/3]-[],sta,[4/6,0/3]-[],des,[0/6]-[4/6],stop,recommend_dose(1)].
[sta,[0/3]-[0/0],esc,[1/3,0/3]-[],sta,[4/6,0/3]-[],des,[1/6]-[4/6],stop,recommend_dose(1)].
[sta,[0/3]-[0/0],esc,[1/3,0/3]-[],sta,[4/6,0/3]-[],des,[2/6]-[4/6],stop,recommend_dose(0)].
[sta,[0/3]-[0/0],esc,[1/3,0/3]-[],sta,[4/6,0/3]-[],des,[3/6]-[4/6],stop,recommend_dose(0)].
[sta,[0/3]-[0/0],esc,[2/3,0/3]-[],des,[0/6]-[2/3],stop,recommend_dose(1)].
[sta,[0/3]-[0/0],esc,[2/3,0/3]-[],des,[1/6]-[2/3],stop,recommend_dose(1)].
[sta,[0/3]-[0/0],esc,[2/3,0/3]-[],des,[2/6]-[2/3],stop,recommend_dose(0)].
[sta,[0/3]-[0/0],esc,[2/3,0/3]-[],des,[3/6]-[2/3],stop,recommend_dose(0)].
[sta,[0/3]-[0/0],esc,[3/3,0/3]-[],des,[0/6]-[3/3],stop,recommend_dose(1)].
[sta,[0/3]-[0/0],esc,[3/3,0/3]-[],des,[1/6]-[3/3],stop,recommend_dose(1)].
[sta,[0/3]-[0/0],esc,[3/3,0/3]-[],des,[2/6]-[3/3],stop,recommend_dose(0)].
[sta,[0/3]-[0/0],esc,[3/3,0/3]-[],des,[3/6]-[3/3],stop,recommend_dose(0)].
[sta,[1/3]-[0/0],sta,[1/6]-[0/0],esc,[0/3,1/6]-[],sta,[0/6,1/6]-[],stop,recommend_dose(2)].
[sta,[1/3]-[0/0],sta,[1/6]-[0/0],esc,[0/3,1/6]-[],sta,[1/6,1/6]-[],stop,recommend_dose(2)].
[sta,[1/3]-[0/0],sta,[1/6]-[0/0],esc,[0/3,1/6]-[],sta,[2/6,1/6]-[],stop,recommend_dose(1)].
[sta,[1/3]-[0/0],sta,[1/6]-[0/0],esc,[0/3,1/6]-[],sta,[3/6,1/6]-[],stop,recommend_dose(1)].
[sta,[1/3]-[0/0],sta,[1/6]-[0/0],esc,[1/3,1/6]-[],sta,[1/6,1/6]-[],stop,recommend_dose(2)].
[sta,[1/3]-[0/0],sta,[1/6]-[0/0],esc,[1/3,1/6]-[],sta,[2/6,1/6]-[],stop,recommend_dose(1)].
[sta,[1/3]-[0/0],sta,[1/6]-[0/0],esc,[1/3,1/6]-[],sta,[3/6,1/6]-[],stop,recommend_dose(1)].
[sta,[1/3]-[0/0],sta,[1/6]-[0/0],esc,[1/3,1/6]-[],sta,[4/6,1/6]-[],stop,recommend_dose(1)].
[sta,[1/3]-[0/0],sta,[1/6]-[0/0],esc,[2/3,1/6]-[],stop,recommend_dose(1)].
[sta,[1/3]-[0/0],sta,[1/6]-[0/0],esc,[3/3,1/6]-[],stop,recommend_dose(1)].
[sta,[1/3]-[0/0],sta,[2/6]-[0/0],stop,recommend_dose(0)].
[sta,[1/3]-[0/0],sta,[3/6]-[0/0],stop,recommend_dose(0)].
[sta,[1/3]-[0/0],sta,[4/6]-[0/0],stop,recommend_dose(0)].
[sta,[2/3]-[0/0],stop,recommend_dose(0)].
[sta,[3/3]-[0/0],stop,recommend_dose(0)].
   J = 46.
*/
