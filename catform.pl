% Inline code for Categorical sketch

:- use_module(library(lists)).
:- use_module(library(clpz)).
:- use_module(library(reif)).
:- use_module(library(dcgs)).
:- use_module(library(error)).
:- use_module(library(si)).
:- use_module(library(lambda)).
:- use_module(library(pairs)).
:- use_module(library(assoc)).
:- use_module(library(time)).
:- use_module(library(format)).
:- use_module(library(debug)).
:- use_module(library(tabling)).
:- use_module(library(iso_ext)).

:- use_module(rcpearl).

clpz:monotonic.

:- op(900, xfx, '≤'). % Mutually exclusive infix
:- op(900, xfx, '≰'). % relations defined on ℕᴰ.

'≤'([], [], true). % trivial case makes general clause easier to implement
'≤'([X|Xs], [Y|Ys], Truth) :- % ≤ extended to ℕᴰ, D≥1
    % TODO: Would reif:cond_t/3 apply here?
    if_(clpz_t(#X #=< #Y),
        '≤'(Xs,Ys,Truth),
        Truth = false
       ).
    
%?- '≤'([], [], Truth).
%@    Truth = true. % A quirk easily excluded from ('≤')/2

%?- '≤'([2], [3], Truth).
%@    Truth = true.

%?- '≤'([2], [3], true).
%@    true.

%?- '≤'([2], [3], false).
%@    false.

Xs '≤' Ys :-
    same_length(Xs, Ys),
    length(Xs, D), D #> 0,
    '≤'(Xs, Ys, true).

%?- [] '≤' [].
%@    false. % As desired

%?- [2] '≤' [3].
%@    true.

%?- [3] '≤' [2].
%@    false.

%?- [2,3] '≤' [3,2].
%@    false.

%?- [2,3] '≤' [3,X].
%@    clpz:(X in 3..sup).

%?- [0,0,0] '≤' Xs, Xs '≤' [1,1,1], label(Xs).
%@    Xs = [0,0,0]
%@ ;  Xs = [0,0,1]
%@ ;  Xs = [0,1,0]
%@ ;  Xs = [0,1,1]
%@ ;  Xs = [1,0,0]
%@ ;  Xs = [1,0,1]
%@ ;  Xs = [1,1,0]
%@ ;  Xs = [1,1,1].


Xs '≰' Ys :-
    same_length(Xs, Ys),
    length(Xs, D), D #> 0,
    '≤'(Xs, Ys, false).

%?- [1,1,1] '≰' Xs.
%@    Xs = [_A,_B,_C], clpz:(_A in inf..0)
%@ ;  Xs = [_A,_B,_C], clpz:(_A in 1..sup), clpz:(_B in inf..0)
%@ ;  Xs = [_A,_B,_C], clpz:(_A in 1..sup), clpz:(_B in 1..sup), clpz:(_C in inf..0)
%@ ;  false.

%% 1. Via Fact 2.13, define evident-$afety relation ≼ ⊂ 𝒬✕𝒬:
:- op(900, xfx, '≼').
:- op(900, xfx, '⋠').
:- op(900, xfx, '≽'). % TODO: If I don't eventually find good uses
:- op(900, xfx, '⋡'). %       for these flipped ops, delete them.

% TODO: Consider implementing also the *strict* orders '≺' and '≻',
%       but watch out in case this introduces subtle misconceptions
%       due to any 'excessive' suggestiveness of these symbols!
:- op(900, xfx, '≺').
:- op(900, xfx, '⊀').
:- op(900, xfx, '≻').
:- op(900, xfx, '⊁').

q_r(T/N, T:U) :- 0 #=< #T, 0 #=< #U, #N #= #T + #U.

qs_Ts_Us(Qs, ΣTs, ΣUs) :-
    maplist(\Q^T^U^(q_r(Q, T:U)), Qs, Ts, Us),
    intlist_partsums(Ts, ΣTs),
    intlist_partsums(Us, ΣUs).

%?- qs_Ts_Us([1/6,2/6], Ts, Us).
%@    Ts = [1,3], Us = [5,9].

'≼'(Q1s, Q2s, Truth) :-
    qs_Ts_Us(Q1s, ST1s, SU1s),
    qs_Ts_Us(Q2s, ST2s, SU2s),
    if_((ST2s '≤' ST1s,
         SU1s '≤' SU2s),
        Truth = true,
        Truth = false
       ).

'≺'(Q1s, Q2s, Truth) :-
    if_((Q1s '≼' Q2s, dif(Q1s, Q2s)),
        Truth = true,
        Truth = false
        ).

'≽'(Q2s, Q1s, Truth) :-'≼'(Q1s, Q2s, Truth).
'≻'(Q2s, Q1s, Truth) :-'≺'(Q1s, Q2s, Truth).

'≼'(Q1s, Q2s) :- '≼'(Q1s, Q2s, true).
'⋠'(Q1s, Q2s) :- '≼'(Q1s, Q2s, false).
'≽'(Q2s, Q1s) :- '≼'(Q1s, Q2s, true).
'⋡'(Q2s, Q1s) :- '≼'(Q1s, Q2s, false).

'≺'(Q1s, Q2s) :- '≺'(Q1s, Q2s, true).
'⊀'(Q1s, Q2s) :- '≺'(Q1s, Q2s, false).
'≻'(Q2s, Q1s) :- '≺'(Q1s, Q2s, true).
'⊁'(Q2s, Q1s) :- '≺'(Q1s, Q2s, false).

%% Utility predicates used above:

intlist_partsums([X|Xs], [X|Ss]) :-
    same_length(Xs, Ss), % eliminate unnecessary choice point
    intlist_partsums_acc(Xs, Ss, X).

intlist_partsums_acc([], [], _).
intlist_partsums_acc([X|Xs], [S|Ss], A) :-
    #S #= #X + #A,
    intlist_partsums_acc(Xs, Ss, S).

%?- [1/3, 1/2] '≼' [0/4, 0/1].
%@    true.

%?- [1/6,1/6] '≼' [0/6,2/6].
%@    true.

%?- [1/6,1/6] '≼' [0/6,2/5].
%@    false.

%?- [1/6,1/6] '≼' [0/6,2/7].
%@    true.

%?- [0/6,2/6] '≽' [1/6,1/6].
%@    true.

%?- [1/3,1/3] '≼' [1/3,1/3].
%@    true.

%?- [1/3,1/3] '≺' [1/3,1/3].
%@    false.

%?- [1/6,1/6] '≺' [0/6,2/6].
%@    true.

:- table d_endtally_rec/3.

% This predicate describes precisely the final tallies and dose recommendations
% which terminate the paths of the D-dose 3+3 design as described by our DCG.
% Memoizing it via *tabling* supports a _complete_ description at the cost of
% only a single, one-off comprehensive elaboration of the DCG.
d_endtally_rec(D, FinalTally, Rec) :-
    length(Init, D), maplist(=(0/0), Init), Init = [I|Is],
    phrase(path([I]-Is), Path),
    phrase((..., [Endstate,stop,recommend_dose(Rec)]), Path),
    state_tallies(Endstate, FinalTally).
    
%?- d_endtally_rec(2, Q, D).
%@    Q = [0/3,0/6], D = 2
%@ ;  Q = [0/3,1/6], D = 2
%@ ;  Q = [0/6,2/3], D = 1
%@ ;  Q = [0/6,2/6], D = 1
%@ ;  Q = [0/6,3/3], D = 1
%@ ;  Q = [0/6,3/6], D = 1
%@ ;  Q = [0/6,4/6], D = 1
%@ ;  Q = [1/6,0/6], D = 2
%@ ;  Q = [1/6,1/6], D = 2
%@ ;  Q = [1/6,2/3], D = 1
%@ ;  Q = [1/6,2/6], D = 1
%@ ;  Q = [1/6,3/3], D = 1
%@ ;  Q = [1/6,3/6], D = 1
%@ ;  Q = [1/6,4/6], D = 1
%@ ;  Q = [2/3,0/0], D = 0
%@ ;  Q = [2/6,0/0], D = 0
%@ ;  Q = [2/6,2/3], D = 0
%@ ;  Q = [2/6,2/6], D = 0
%@ ;  Q = [2/6,3/3], D = 0
%@ ;  Q = [2/6,3/6], D = 0
%@ ;  Q = [2/6,4/6], D = 0
%@ ;  Q = [3/3,0/0], D = 0
%@ ;  Q = [3/6,0/0], D = 0
%@ ;  Q = [3/6,2/3], D = 0
%@ ;  Q = [3/6,2/6], D = 0
%@ ;  Q = [3/6,3/3], D = 0
%@ ;  Q = [3/6,3/6], D = 0
%@ ;  Q = [3/6,4/6], D = 0
%@ ;  Q = [4/6,0/0], D = 0
%@ ;  false.

% Now we readily "check the functoriality" of the dose recommendations
/*
?- d_endtally_rec(2, Q1, D1),
   d_endtally_rec(2, Q2, D2),
   Q1 '≼' Q2, % Q1 evidently no safer than Q2,
   D1 #>  D2. % yet recommended D1 exceeds D2.
%@    Q1 = [1/6,1/6], D1 = 2, Q2 = [0/6,2/6], D2 = 1
%@ ;  false.
*/

% A different way to put this would be:
/*
?- d_endtally_rec(2, Q1, D1),
   d_endtally_rec(2, Q2, D2),
      Q1 '≼' Q2,  % Q1 is evidently no safer than Q2,
   #\(D1 #=< D2). % yet D1 is NOT likewise related to D2.
%@    Q1 = [1/6,1/6], D1 = 2, Q2 = [0/6,2/6], D2 = 1
%@ ;  false.
*/

% That initial listing in Section 4.1 ought to have been done with
% this predicate too!
/*
?- N+\(setof(Q-Rec, d_endtally_rec(2, Q, Rec), QRecs),
       maplist(portray_clause, QRecs),
       length(QRecs, N)).
%@ [0/3,0/6]-2.
%@ [0/3,1/6]-2.
%@ [0/6,2/3]-1.
%@ [0/6,2/6]-1.
%@ [0/6,3/3]-1.
%@ [0/6,3/6]-1.
%@ [0/6,4/6]-1.
%@ [1/6,0/6]-2.
%@ [1/6,1/6]-2.
%@ [1/6,2/3]-1.
%@ [1/6,2/6]-1.
%@ [1/6,3/3]-1.
%@ [1/6,3/6]-1.
%@ [1/6,4/6]-1.
%@ [2/3,0/0]-0.
%@ [2/6,0/0]-0.
%@ [2/6,2/3]-0.
%@ [2/6,2/6]-0.
%@ [2/6,3/3]-0.
%@ [2/6,3/6]-0.
%@ [2/6,4/6]-0.
%@ [3/3,0/0]-0.
%@ [3/6,0/0]-0.
%@ [3/6,2/3]-0.
%@ [3/6,2/6]-0.
%@ [3/6,3/3]-0.
%@ [3/6,3/6]-0.
%@ [3/6,4/6]-0.
%@ [4/6,0/0]-0.
%@    N = 29.
*/

% Clearly, some of these 29 final tallies must be shared
% between several of the 46 distinct trial paths.
% Let's demonstrate how!

endtally_path(FinalTally, Path) :-
    phrase(path([0/0]-[0/0]), Path),
    phrase((..., [Endstate,stop,recommend_dose(_)]), Path),
    state_tallies(Endstate, FinalTally).

%?- endtally_path(Q, P).
%@    Q = [0/3,0/6], P = [sta,[0/3]-[0/0],esc,[0/3,0/3]-[],sta,[0/6,0/3]-[],stop,recommend_dose(2)]
%@ ;  Q = [0/3,1/6], P = [sta,[0/3]-[0/0],esc,[0/3,0/3]-[],sta,[1/6,0/3]-[],stop,recommend_dose(2)]
%@ ;  ... .

/*
It's time now to investigate what trial designs arise from
a rectified tally-dose mapping.  We are looking for all
incremental enrollments that are consistent with the
preorder obtained 
*/

/*
?- d_mendtally_rec(2, Q1, D1),
   d_mendtally_rec(2, Q2, D2),
   Q1 '≼' Q2, % Q1 evidently no safer than Q2,
   D1 #>  D2. % yet recommended D1 exceeds D2.
%@    false. % Rectification was successful.
*/

% Some good visualizations would seem to be necessary now
% to promote efficient progress.  What Hasse diagrams could
% we draw for the partial order ≼ restricted to final tallies?
% Note that it could be interesting to define Hasse diagrams
% declaratively, and have Prolog find *all* of them for me.
% But to begin, let's explore some special solutions yielded
% by specific heuristics.

% Suppose we take a list (qua set) of all final tallies, and
% recursively peel off the minimal elements, i.e. those which
% have no arrows into the remainder.
minimal_in(M, Qs) :-
    member(M, Qs),
    maplist('⊁'(M), Qs).

/*
?- Ms+\(findall(Q, d_mendtally_rec(2,Q,_), FinalTallies),
        findall(M, minimal_in(M, FinalTallies), Ms)).
%@    Ms = [[3/3,0/0],[3/6,3/3],[3/6,4/6],[4/6,0/0]].
*/

% The https://en.wikipedia.org/wiki/Covering_relation is
% fundamental, and surely warrants a dedicated predicate.
% NB: The time-complexity of in_cover_t/3 could be reduced
%     by exploiting the arithmetized sort behind d_strata/2.
%     But we retain this implementation for the time being,
%     since its simplicity renders it 'obviously' correct.
in_cover_t(Qs, Q1, Q2, Truth) :-
    member(Q1, Qs),
    member(Q2, Qs),
    Q1 '≺' Q2,
    if_(tmember_t(between_t(Q1,Q2), Qs),
        Truth = false,
        Truth = true
       ).

between_t(Q1, Q2, Q, Truth) :-
    if_((Q1 '≺' Q, Q '≺' Q2),
        Truth = true,
        Truth = false
       ).

in_cover(Qs, Q1, Q2) :- in_cover_t(Qs, Q1, Q2, true).

d_ncovers(D, N) :-
    findall(Q, d_mendtally_rec(D,Q,_), Qs),
    findall(Q1-Q2, in_cover(Qs, Q1, Q2), Covers),
    length(Covers, N).

%?- time(d_ncovers(2, N)).
%@    % CPU time: 8.045s, 40_522_204 inferences
%@    N = 50.

%?- time(d_ncovers(3, N)).
%@    % CPU time: 242.710s, 1_230_061_670 inferences
%@    N = 194.

% At least for the D=2 case, a useful Hasse diagram for 𝒬f seems within reach.
% One thing that could be of special help would be finding small sets of q's
% that share the same covered and covering elements, since these could be
% collected into single nodes of the Hasse diagram.
% As a step toward finding any such little collections, let me partition 𝒬f
% into a list of recursively peeled-off minimal sets.

%?- findall(Q, d_mendtally_rec(2, Q, _), Qs), findall(Qm, minimal_in(Qm, Qs), Qms).
%@    Qs = [[0/3,0/6],[0/3,1/6],[0/6,2/3],[0/6,2/6],[0/6,3/3],[0/6,3/6],[0/6,4/6],[1/6,0/6],[1/6,1/6],[1/6,2/3],[1/6,2/6],[1/6,3/3],[1/6,3/6],[1/6,4/6],[2/3,0/0],[2/6,0/0],[2/6,2/3],[2/6,2/6],[2/6,... / ...],[... / ...|...]|...], Qms = [[3/3,0/0],[3/6,3/3],[3/6,4/6],[4/6,0/0]].

% By embedding the partial order ≼ into a *complete* order,
% I could sort 𝒬f so that all arrows of ≼ point left-to-right.
% Then, minimal sets would be in contiguous stretches of this
% sorted list, and identifying the partitions could be done
% potentially quite efficiently.

% I would expect that this list of (recursively) minimal sets
% would itself be useful for computing the covering relation.
% (Exactly *how* it would help remains to be discovered.)

% One way to obtain a complete order would be to arithmetize
% the tallies.

% Let's try a more compact embedding of 𝒬 ↪ (ℕ,≤) ...

% To begin, let's just encode a vector (X_1,..,X_D), where Xn ∈ 0..(6*n).
% This corresponds to a 'variable-base' number where the nth 'place' has
% a 'digit' with value in 0..Mn, with Mn = 6n.
% The _value_ of the nth place in such a number is the product
%   Pn = B1*...*B_{n-1}, n ∈ 0..(D-1).
% For example, the D=3 case would have
%   K = X1 + B1*(X2 + B2*(X3)) = X1 + B1*X2 + B1*B2*X3.
% The general case can be developed more easily by defining the products
%   Pn = B1*...*Bn, for n in 1..D-1.
% Then we have
%   P1 = 1, P2 = B1, ..., P_D = B1*...*B_{D-1}
%   K = P1*X1 + P2*X2 + P3*X3.
% The values (X1,...,XD) may then be recovered from K by repeated
% division-with-remainder operations.

% Could I start with a good, recursive definition of the Ps?
% I think I want to build the list in descending order, so that
% P1 goes deepest, P2 above it, and so on.
% This correlates best with our normal way of writing numbers,
% putting MSD's leftmost and LSD's rightmost.

pvs([P|Ps]) :-
    pvs(Ps),
    pvs_nextup(Ps, P).
pvs([]).

pvs_nextup([], 1).
pvs_nextup([P|Ps], P1) :-
    length([P|Ps], N),
    #P1 #= #P * (6*N + 1).

% Let's just PRECOMPUTE!
%?- length(Ps, 8), pvs(Ps), reverse(Ps, Rs).
%@    Ps = [2131900225,49579075,1339975,43225,1729,91,7,1], Rs = [1,7,91,1729,43225,1339975,49579075,2131900225].

placevalues(Ps) :-
    same_length(Ps, Rs),
    % NB: Taking a _tail_ with append/3 would leave a choice point.
    append(Rs, _, [1,7,91,1729,43225,1339975,49579075,2131900225]),
    reverse(Rs, Ps).

%?- length(Ps, 5), placevalues(Ps).
%@    Ps = [43225,1729,91,7,1].

% At this point, the encoding is extremely straightforward.
%?- scalar_product([1,2,3], [4,5,6], #=, #Ooh).
%@    Ooh = 32.

ws_int(Ws, K) :-
    same_length(Ws, Ps),
    placevalues(Ps),
    reverse(Ws, RWs), % our Us and Ts are typically indexed 1..D
    scalar_product(RWs, Ps, #=, #K).

%?- ws_int([3,7,13], K).
%@    K = 1235.

%?- #W1 #= 1235 mod 7.
%@    W1 = 3.

%?- #W2 #= (1235 div 7) mod 13.
%@    W2 = 7.

%?- #W3 #= (1235 div 7) div 13.
%@    W3 = 13.

%?- placevalues([P3,P2,P1]).
%@    P3 = 91, P2 = 7, P1 = 1.

%?- #K #= 91*13 + 7*7 + 3.
%@    K = 1235.

%?- #W3 #= 1235 div 91.
%@    W3 = 13.

%?- #W2 #= (1235 mod 91) div 7.
%@    W2 = 7.

%?- #W1 #= ((1235 mod 91) mod 7) div 1.
%@    W1 = 3.

% Finally, I need to write int_ws/2 implementing the _decoding_.
% Again, I will suppose Ws is an uninstantiated list that is
% however of known length.

% Ah, after our afternoon walk (70F!) I see that the needed predicate is:
int_bases_digits(K, [B|Bs], [W|Ws]) :-
    same_length(Bs, Ws),
    #W #= #K mod #B,
    #K1 #= #K div #B,
    int_bases_digits(K1, Bs, Ws).

int_bases_digits(_, [], []). % ... or something like that!

%?- int_bases_digits(Y, [], []).
%@    true.

%?- int_bases_digits(1023, [2,2,2,2,2,2,2,2,2,2], Ds).
%@    Ds = [1,1,1,1,1,1,1,1,1,1].

%?- int_bases_digits(1023, [16,16,2,2], Ds).
%@    Ds = [15,15,1,1].

%?- int_bases_digits(1235, [7,13,19], Ws).
%@    Ws = [3,7,13].

% The length-D list of bases starts with 6 + 1 = 7,
% and adds 6 at each level.  What is the simplest way
% to create such an arithmetic sequence in Prolog?
d_bases(D, [B|Bs]) :-
    length([B|Bs], D),
    same_length(Xs, Bs),
    maplist(=(6), Xs),
    intlist_partsums([7|Xs], [B|Bs]).

d_int_ws(D, K, Ws) :-
    d_bases(D, Bs),
    int_bases_digits(K, Bs, Ws).
    
%?- d_bases(3, Bs).
%@    Bs = [7,13,19].

%?- d_int_ws(3, 1235, Ws).
%@    Ws = [3,7,13].

% What about complements in general?

%?- ws_int([1,2,3,4,5], K).
%@    K = 223329.

%?- ws_int([1,2,3,4,5], K).
%@    K = 223329.

%% d_maxenc(D, Kmax) :-
%%     length(Ps, D),
%%     placevalues([Kmax1|Ps]),
%%     #Kmax #= Kmax1 - 1.

%?- d_maxenc(5, Kmax).
%@    Kmax = 1339974.

% I've already precomputed placevalues/1, but might I still
% gain additional speedup by precomputing d_maxenc/2 also?
%?- d_maxenc(D, Kmax).
%@    D = 0, Kmax = 0
%@ ;  D = 1, Kmax = 6
%@ ;  D = 2, Kmax = 90
%@ ;  D = 3, Kmax = 1728
%@ ;  D = 4, Kmax = 43224
%@ ;  D = 5, Kmax = 1339974
%@ ;  D = 6, Kmax = 49579074
%@ ;  D = 7, Kmax = 2131900224
%@ ;  error('$interrupt_thrown',repl/0).

d_maxenc(1, 6).
d_maxenc(2, 90).
d_maxenc(3, 1728).
d_maxenc(4, 43224).
d_maxenc(5, 1339974).
d_maxenc(6, 49579074).
d_maxenc(7, 2131900224).

%?- d_maxenc(5, Kmax).
%@    Kmax = 1339974.

% NB: We could encode D=7 tallies in 62-bit integers!
%?- #M #= 2^31, d_maxenc(7, Kmax), M > Kmax.
%@    M = 2147483648, Kmax = 2131900224.

ws_cint(Ws, CK) :-
    ws_int(Ws, K),
    length(Ws, D),
    d_maxenc(D, Kmax),
    #CK #= #Kmax - #K.

%?- ws_cint([5,10,15,20,25], CK).
%@    CK = 223329.

%?- ws_int([1,2,3,4,5], CK).
%@    CK = 223329.

% Finally, I need to encode Ts-Us pairs _jointly_.
qs_int(Qs, K) :-
    %format("qs_Ts_Us/3 ..", []), time(qs_Ts_Us(Qs, Ts, Us)),
    %format("ws_int/2 ....", []), time(ws_int(Ts, KT)),
    %format("ws_cint/2 ...", []), time(ws_cint(Us, CKU)),
    qs_Ts_Us(Qs, Ts, Us),
    ws_int(Ts, KT),
    ws_cint(Us, CKU),
    length(Qs, D),
    %format("d_maxenc/2 ..", []), time(d_maxenc(D, Kmax)),
    d_maxenc(D, Kmax),
    #Kmax1 #= #Kmax + 1,
    #K #= #Kmax1 * #KT + #CKU.

/*
?- Qs=[1/6,0/3,2/6], qs_int(Qs, K).
%@ qs_Ts_Us/3 ..   % CPU time: 0.001s, 2_333 inferences
%@ ws_int/2 ....   % CPU time: 0.000s, 920 inferences
%@ ws_cint/2 ...   % CPU time: 0.000s, 940 inferences
%@ d_maxenc/2 ..   % CPU time: 0.000s, 1 inference
%@    Qs = [1/6,0/3,2/6], K = 486424.
%@ qs_Ts_Us/3 ..   % CPU time: 0.002s, 2_333 inferences
%@ ws_int/2 ....   % CPU time: 0.000s, 920 inferences
%@ ws_cint/2 ...   % CPU time: 0.000s, 1_618 inferences
%@ d_maxenc/2 ..   % CPU time: 0.000s, 1 inference
%@    Qs = [1/6,0/3,2/6], K = 486424.
%@ qs_Ts_Us/3 ..   % CPU time: 0.001s, 2_333 inferences
%@ ws_int/2 ....   % CPU time: 0.000s, 920 inferences
%@ ws_cint/2 ...   % CPU time: 0.001s, 1_618 inferences
%@ d_maxenc/2 ..   % CPU time: 0.000s, 1 inference
%@    Qs = [1/6,0/3,2/6], K = 486424.
%@    Qs = [1/6,0/3,2/6], K = 486424
%@ ;  false.
%@ qs_Ts_Us/3 ..   % CPU time: 0.003s, 2_356 inferences
%@ ws_int/2 ....   % CPU time: 0.000s, 1_473 inferences
%@ ws_cint/2 ...   % CPU time: 0.001s, 3_527 inferences
%@ d_maxenc/2 ..   % CPU time: 0.000s, 1_367 inferences
%@    Qs = [1/6,0/3,2/6], K = 486424
%@ ;  % CPU time: 0.000s, 35 inferences
%@    % CPU time: 0.000s, 66 inferences
%@    % CPU time: 0.000s, 31 inferences
%@    false.
%@ qs_Ts_Us/3 ..   % CPU time: 0.001s, 2_333 inferences
%@ ws_int/2 ....   % CPU time: 0.004s, 16_401 inferences
%@ ws_cint/2 ...   % CPU time: 0.002s, 9_074 inferences
%@ d_maxenc/2 ..   % CPU time: 0.000s, 1_367 inferences
%@    Qs = [1/6,0/3,2/6], K = 486424
%@ ;  % CPU time: 0.000s, 35 inferences
%@    % CPU time: 0.000s, 66 inferences
%@    % CPU time: 0.000s, 31 inferences
%@    false.
%@ qs_Ts_Us/3 ..   % CPU time: 0.001s, 2_333 inferences
%@ ws_int/2 ....   % CPU time: 0.002s, 7_854 inferences
%@ ws_cint/2 ...   % CPU time: 0.004s, 17_694 inferences
%@ d_maxenc/2 ..   % CPU time: 0.002s, 9_143 inferences
%@    Qs = [1/6,0/3,2/6], K = 486424.
%@    Qs = [1/6,0/3,2/6], Ts = [1,1,3], Us = [5,8,12], KT = 281, CKU = 575.
%@    Qs = [1/6,0/3,2/6], Ts = [1,1,3], Us = [5,8,12], KT = 281, CKU = 575
%@ ;  false. % Aha, now I find a choicepoint inside ws_cint/2!
%@    Qs = [1/6,0/3,2/6], Ts = [1,1,3], Us = [5,8,12], KT = 281.
%@    Qs = [1/6,0/3,2/6], Ts = [1,1,3], Us = [5,8,12].
%@ qs_Ts_Us/3 ..   % CPU time: 0.003s, 2_333 inferences
%@ ws_int/2 ....   % CPU time: 0.003s, 7_854 inferences
%@ ws_cint/2 ...   % CPU time: 0.005s, 19_615 inferences
%@ d_maxenc/2 ..   % CPU time: 0.000s, 281 inferences
%@    Qs = [1/6,0/3,2/6], K = 486424
%@ ;  % CPU time: 0.000s, 19 inferences
%@    % CPU time: 0.000s, 19 inferences
%@    false.
%@    Qs = [1/6,0/3,2/6], Ts = [1,1,3], Us = [5,8,12], KT = 281.
%@    Qs = [1/6,0/3,2/6], Ts = [1,1,3], Us = [5,8,12], KT = 281
%@ ;  false. % Aha, choicepoint is in ws_int
%@    Qs = [1/6,0/3,2/6], Ts = [1,1,3], Us = [5,8,12].
%@ qs_Ts_Us/3 ..   % CPU time: 0.003s, 2_356 inferences
%@ ws_int/2 ....   % CPU time: 0.000s, 1_473 inferences
%@ ws_cint/2 ...   % CPU time: 0.000s, 2_448 inferences
%@ d_maxenc/2 ..   % CPU time: 0.000s, 288 inferences
%@    Qs = [1/6,0/3,2/6], K = 486424
%@ ;  % CPU time: 0.000s, 19 inferences
%@    % CPU time: 0.000s, 50 inferences
%@    % CPU time: 0.000s, 31 inferences
%@    false.
*/

%?- Qs=[1/6,0/3,2/6], time(qs_int(Qs, K)). % now TABLING d_maxenc/2 also
%@ qs_Ts_Us/3 ..   % CPU time: 0.003s, 2_356 inferences
%@ ws_int/2 ....   % CPU time: 0.000s, 1_473 inferences
%@ ws_cint/2 ...   % CPU time: 0.001s, 2_448 inferences
%@ d_maxenc/2 ..   % CPU time: 0.000s, 288 inferences
%@    % CPU time: 0.015s, 14_222 inferences
%@    Qs = [1/6,0/3,2/6], K = 486424
%@ ;  % CPU time: 0.000s, 19 inferences
%@    % CPU time: 0.000s, 50 inferences
%@    % CPU time: 0.000s, 31 inferences
%@    % CPU time: 0.010s, 5_332 inferences
%@    false. % New choice point; why?
%@ qs_Ts_Us/3 ..   % CPU time: 0.000s, 2_356 inferences
%@ ws_int/2 ....   % CPU time: 0.005s, 16_480 inferences
%@ ws_cint/2 ...   % CPU time: 0.001s, 6_878 inferences
%@ d_maxenc/2 ..   % CPU time: 0.000s, 288 inferences
%@    % CPU time: 0.014s, 33_656 inferences
%@    Qs = [1/6,0/3,2/6], K = 486424
%@ ;  % CPU time: 0.000s, 19 inferences
%@    % CPU time: 0.000s, 50 inferences
%@    % CPU time: 0.000s, 31 inferences
%@    % CPU time: 0.010s, 5_332 inferences
%@    false.

%?- Qs=[1/6,0/3,2/6], time(qs_int(Qs, K)). % now TABLING d_placevalues/2
%@ qs_Ts_Us/3 ..   % CPU time: 0.002s, 2_356 inferences
%@ ws_int/2 ....   % CPU time: 0.000s, 1_473 inferences
%@ ws_cint/2 ...   % CPU time: 0.002s, 4_912 inferences
%@ d_maxenc/2 ..   % CPU time: 0.000s, 2_752 inferences
%@    % CPU time: 0.015s, 19_172 inferences
%@    Qs = [1/6,0/3,2/6], K = 486424
%@ ;  % CPU time: 0.000s, 31 inferences
%@    % CPU time: 0.000s, 62 inferences
%@    % CPU time: 0.000s, 31 inferences
%@    % CPU time: 0.011s, 5_356 inferences
%@    false.
%@ qs_Ts_Us/3 ..   % CPU time: 0.001s, 2_356 inferences
%@ ws_int/2 ....   % CPU time: 0.004s, 16_480 inferences
%@ ws_cint/2 ...   % CPU time: 0.001s, 4_912 inferences
%@ d_maxenc/2 ..   % CPU time: 0.000s, 2_752 inferences
%@    % CPU time: 0.015s, 34_176 inferences
%@    Qs = [1/6,0/3,2/6], K = 486424
%@ ;  % CPU time: 0.000s, 31 inferences
%@    % CPU time: 0.000s, 62 inferences
%@    % CPU time: 0.000s, 31 inferences
%@    % CPU time: 0.009s, 5_356 inferences
%@    false.
%@ qs_Ts_Us/3 ..   % CPU time: 0.002s, 2_356 inferences
%@ ws_int/2 ....   % CPU time: 0.000s, 1_492 inferences
%@ ws_cint/2 ...   % CPU time: 0.001s, 4_950 inferences
%@ d_maxenc/2 ..   % CPU time: 0.000s, 2_771 inferences
%@    % CPU time: 0.014s, 19_248 inferences
%@    Qs = [1/6,0/3,2/6], K = 486424
%@ ;  % CPU time: 0.000s, 31 inferences
%@    % CPU time: 0.000s, 62 inferences
%@    % CPU time: 0.000s, 31 inferences
%@    % CPU time: 0.009s, 5_356 inferences
%@    false.
%@ qs_Ts_Us/3 ..   % CPU time: 0.001s, 2_356 inferences
%@ ws_int/2 ....   % CPU time: 0.008s, 17_777 inferences
%@ ws_cint/2 ...   % CPU time: 0.002s, 4_950 inferences
%@ d_maxenc/2 ..   % CPU time: 0.001s, 2_771 inferences
%@    % CPU time: 0.025s, 35_530 inferences
%@    Qs = [1/6,0/3,2/6], K = 486424
%@ ;  % CPU time: 0.000s, 31 inferences
%@    % CPU time: 0.000s, 62 inferences
%@    % CPU time: 0.000s, 31 inferences
%@    % CPU time: 0.013s, 5_356 inferences
%@    false.

%?- Qs=[1/6,0/3,2/6], time(qs_int(Qs, K)). % AFTER placevalues/1 ~~> d_placevalues/2
%@ qs_Ts_Us/3 ..   % CPU time: 0.001s, 2_356 inferences
%@ ws_int/2 ....   % CPU time: 0.001s, 6_338 inferences
%@ ws_cint/2 ...   % CPU time: 0.003s, 14_662 inferences
%@ d_maxenc/2 ..   % CPU time: 0.001s, 7_627 inferences
%@    % CPU time: 0.016s, 38_770 inferences
%@    Qs = [1/6,0/3,2/6], K = 486424.

%?- Qs=[1/6,0/3,2/6], time(qs_int(Qs, K)).
%@ qs_Ts_Us/3 ..   % CPU time: 0.001s, 2_356 inferences
%@ ws_int/2 ....   % CPU time: 0.002s, 5_049 inferences
%@ ws_cint/2 ...   % CPU time: 0.005s, 12_084 inferences
%@ d_maxenc/2 ..   % CPU time: 0.002s, 6_338 inferences
%@    % CPU time: 0.024s, 33_614 inferences
%@    Qs = [1/6,0/3,2/6], K = 486424.
%@    % CPU time: 0.003s, 2_333 inferences
%@    % CPU time: 0.001s, 5_049 inferences
%@    % CPU time: 0.003s, 12_084 inferences
%@    % CPU time: 0.001s, 6_338 inferences
%@    Qs = [1/6,0/3,2/6], K = 486424.
%@    error(existence_error(procedure,qs_int/3),qs_int/3).


%?- Qs=[1/6,2/3], qs_Ts_Us(Qs, Ts, Us).
%@    Qs = [1/6,2/3], Ts = [1,3], Us = [5,6].

%?- Qs=[1/6,2/3], qs_int(Qs, K).
%@    Qs = [1/6,2/3], KT = 22, CKU = 43, K = 2045.

% For the time being, we also need a special, reverse-direction predicate:
d_int_kt_ku(D, K, KT, KU) :-
    d_maxenc(D, Kmax),
    #Kmax1 #= #Kmax + 1,
    #KT #= #K div #Kmax1,
    #CKU #= #K mod #Kmax1,
    #KU #= #Kmax - #CKU.

int_qs(K, Qs) :-
    length(Qs, D),
    d_int_kt_ku(D, K, KT, KU),
    d_int_ws(D, KT, Ts),
    d_int_ws(D, KU, Us),
    qsfrom_Ts_Us(Qs, Ts, Us).

qsfrom_Ts_Us(Qs, CTs, CUs) :- % 'C' for Cumulative
    intlist_partsums(Ts, CTs),
    intlist_partsums(Us, CUs),
    maplist(\T^U^R^(R = T:U), Ts, Us, Rs),
    same_length(Qs, Rs), % eliminates a superfluous choice point
    maplist(q_r, Qs, Rs).

%?- length(Qs, 2), int_qs(2045, Qs).
%@    Qs = [1/6,2/3].

%?- qsfrom_Ts_Us(Qs, [1,3], [5,6]).
%@    Qs = [1/6,2/3].

% We're ready to demonstrate encode and decode as inverses!
%?- qs_int([1/6,0/3,1/3], K), length(Qs, 3), int_qs(K, Qs).
%@    K = 329267, Qs = [1/6,0/3,1/3].

d_sortedQfs(D, SQs) :-
    findall(Q, d_mendtally_rec(D,Q,_), Qs),
    qs_sorted(Qs, SQs).

qs_sorted(Qs, SQs) :-
    format("Encoding Qs... ", []),
    time(maplist(qs_int, Qs, Ks)),
    format("Sorting Qs.... ", []),
    time(sort(Ks, SKs)),
    same_length(SQs, Qs),
    format("Sizing Qs..... ", []),
    time(maplist(same_length, SQs, Qs)),
    format("Decoding...... ", []),
    time(maplist(int_qs, SKs, SQs)).

% After PRECOMPUTING placevalues/1
%?- D=3, findall(Q, qs_d_nmax(Q, D, 6), Qs), time(qs_sorted(Qs, SQs)).
%@ Encoding Qs...    % CPU time: 27.665s, 151_958_265 inferences
%@ Sorting Qs....    % CPU time: 0.019s, 2 inferences
%@ Sizing Qs.....    % CPU time: 0.020s, 175_617 inferences
%@ Decoding......    % CPU time: 49.427s, 314_906_923 inferences
%@    % CPU time: 77.143s, 467_092_723 inferences
%@    D = 3, Qs = [[0/0,0/0,0/0],[0/0,0/0,0/1],[0/0,0/0,1/1],[0/0,0/0,0/2],[0/0,0/0,1/2],[0/0,0/0,2/2],[0/0,0/0,0/3],[0/0,0/0,1/3],[0/0,0/0,2/3],[0/0,0/0,3/3],[0/0,0/0,0/4],[0/0,0/0,1/4],[0/0,0/0,2/4],[0/0,0/0,3/4],[0/0,0/0,4/4],[0/0,0/0,0/5],[0/0,0/0,1/5],[0/0,0/0,... / ...],[0/0,... / ...|...],[... / ...|...]|...], SQs = [[0/6,0/6,0/6],[0/6,0/6,0/5],[0/6,0/5,0/6],[0/5,0/6,0/6],[0/6,0/6,0/4],[0/6,0/5,0/5],[0/5,0/6,0/5],[0/6,0/4,0/6],[0/5,0/5,0/6],[0/4,0/6,0/6],[0/6,0/6,0/3],[0/6,0/5,0/4],[0/5,0/6,0/4],[0/6,0/4,0/5],[0/5,0/5,0/5],[0/4,0/6,0/5],[0/6,0/3,0/6],[0/5,0/4,... / ...],[0/4,... / ...|...],[... / ...|...]|...].

% After tabling d_placevalues/2 ...
%?- D=3, findall(Q, qs_d_nmax(Q, D, 6), Qs), time(qs_sorted(Qs, SQs)).
%@ Encoding Qs...    % CPU time: 38.165s, 204_883_070 inferences
%@ Sorting Qs....    % CPU time: 0.017s, 2 inferences
%@ Sizing Qs.....    % CPU time: 0.020s, 175_617 inferences
%@ Decoding......    % CPU time: 52.788s, 329_439_147 inferences
%@    % CPU time: 91.002s, 534_549_657 inferences
%@    D = 3, Qs = [[0/0,0/0,0/0],[0/0,0/0,0/1],[0/0,0/0,1/1],[0/0,0/0,0/2],[0/0,0/0,1/2],[0/0,0/0,2/2],[0/0,0/0,0/3],[0/0,0/0,1/3],[0/0,0/0,2/3],[0/0,0/0,3/3],[0/0,0/0,0/4],[0/0,0/0,1/4],[0/0,0/0,2/4],[0/0,0/0,3/4],[0/0,0/0,4/4],[0/0,0/0,0/5],[0/0,0/0,1/5],[0/0,0/0,... / ...],[0/0,... / ...|...],[... / ...|...]|...], SQs = [[0/6,0/6,0/6],[0/6,0/6,0/5],[0/6,0/5,0/6],[0/5,0/6,0/6],[0/6,0/6,0/4],[0/6,0/5,0/5],[0/5,0/6,0/5],[0/6,0/4,0/6],[0/5,0/5,0/6],[0/4,0/6,0/6],[0/6,0/6,0/3],[0/6,0/5,0/4],[0/5,0/6,0/4],[0/6,0/4,0/5],[0/5,0/5,0/5],[0/4,0/6,0/5],[0/6,0/3,0/6],[0/5,0/4,... / ...],[0/4,... / ...|...],[... / ...|...]|...]
%@ ;  % CPU time: 0.180s, 768_320 inferences
%@    % CPU time: 0.385s, 2_897_664 inferences
%@    % CPU time: 0.568s, 3_669_656 inferences
%@    false.

% I've discovered qs_sorted/2 accounts for 80% of run-time for d_gs/2 (D=3 case)
%?- D=3, findall(Q, qs_d_nmax(Q, D, 6), Qs), time(qs_sorted(Qs, SQs)).
%@ Encoding Qs...    % CPU time: 101.706s, 580_549_113 inferences
%@ Sorting Qs....    % CPU time: 0.020s, 2 inferences
%@ Sizing Qs.....    % CPU time: 0.019s, 175_617 inferences
%@ Decoding......    % CPU time: 72.479s, 438_562_539 inferences
%@    % CPU time: 174.236s, 1_019_339_176 inferences
%@    D = 3, Qs = [[0/0,0/0,0/0],[0/0,0/0,0/1],[0/0,0/0,1/1],[0/0,0/0,0/2],[0/0,0/0,1/2],[0/0,0/0,2/2],[0/0,0/0,0/3],[0/0,0/0,1/3],[0/0,0/0,2/3],[0/0,0/0,3/3],[0/0,0/0,0/4],[0/0,0/0,1/4],[0/0,0/0,2/4],[0/0,0/0,3/4],[0/0,0/0,4/4],[0/0,0/0,0/5],[0/0,0/0,1/5],[0/0,0/0,... / ...],[0/0,... / ...|...],[... / ...|...]|...], SQs = [[0/6,0/6,0/6],[0/6,0/6,0/5],[0/6,0/5,0/6],[0/5,0/6,0/6],[0/6,0/6,0/4],[0/6,0/5,0/5],[0/5,0/6,0/5],[0/6,0/4,0/6],[0/5,0/5,0/6],[0/4,0/6,0/6],[0/6,0/6,0/3],[0/6,0/5,0/4],[0/5,0/6,0/4],[0/6,0/4,0/5],[0/5,0/5,0/5],[0/4,0/6,0/5],[0/6,0/3,0/6],[0/5,0/4,... / ...],[0/4,... / ...|...],[... / ...|...]|...].

%?- D=2, findall(Q, qs_d_nmax(Q, D, 6), Qs), time(qs_sorted(Qs, SQs)).
%@ Encoding Qs...    % CPU time: 2.410s, 13_546_869 inferences
%@ Sorting Qs....    % CPU time: 0.000s, 2 inferences
%@ Sizing Qs.....    % CPU time: 0.000s, 4_705 inferences
%@ Decoding......    % CPU time: 1.780s, 11_012_059 inferences
%@    % CPU time: 4.197s, 24_573_088 inferences
%@    D = 2, Qs = [[0/0,0/0],[0/0,0/1],[0/0,1/1],[0/0,0/2],[0/0,1/2],[0/0,2/2],[0/0,0/3],[0/0,1/3],[0/0,2/3],[0/0,3/3],[0/0,0/4],[0/0,1/4],[0/0,2/4],[0/0,3/4],[0/0,4/4],[0/0,0/5],[0/0,1/5],[0/0,2/5],[0/0,... / ...],[... / ...|...]|...], SQs = [[0/6,0/6],[0/6,0/5],[0/5,0/6],[0/6,0/4],[0/5,0/5],[0/4,0/6],[0/6,0/3],[0/5,0/4],[0/4,0/5],[0/3,0/6],[0/6,0/2],[0/5,0/3],[0/4,0/4],[0/3,0/5],[0/2,0/6],[0/6,0/1],[0/5,0/2],[0/4,0/3],[0/3,... / ...],[... / ...|...]|...].

% And the above now points to encoding qs_int/2 and decoding int_qs/2
% as accounting for the ENTIRE run-time of qs_sorted/2!

%?- qs_d_nmax(Q, 2, 6).
%@    Q = [0/0,0/0]
%@ ;  Q = [0/0,0/1]
%@ ;  Q = [0/0,1/1]
%@ ;  Q = [0/0,0/2]
%@ ;  Q = [0/0,1/2]
%@ ;  Q = [0/0,2/2]
%@ ;  Q = [0/0,0/3]
%@ ;  ... .

%?- findall(Q, qs_d_nmax(Q, 2, 6), Qs), length(Qs, N).
%@    Qs = [[0/0,0/0],[0/0,0/1],[0/0,1/1],[0/0,0/2],[0/0,1/2],[0/0,2/2],[0/0,0/3],[0/0,1/3],[0/0,2/3],[0/0,3/3],[0/0,0/4],[0/0,1/4],[0/0,2/4],[0/0,3/4],[0/0,4/4],[0/0,0/5],[0/0,1/5],[0/0,2/5],[0/0,... / ...],[... / ...|...]|...], N = 784.
%@    Qs = [[0/0,0/0],[0/0,0/1],[0/0,1/1],[0/0,0/2],[0/0,1/2],[0/0,2/2],[0/0,0/3],[0/0,1/3],[0/0,2/3],[0/0,3/3],[0/1,0/0],[1/1,0/0],[0/1,0/1],[0/1,1/1],[1/1,0/1],[1/1,1/1],[0/1,0/2],[0/1,1/2],[0/1,... / ...],[... / ...|...]|...], N = 100.

%?- D=3, Nmax=6, L+\(findall(Q, qs_d_nmax(Q, D, Nmax), Qs), qs_sorted(Qs, SQs), length(SQs, L)).
%@    error(existence_error(procedure,qs_d_nmax/3),qs_d_nmax/3).

%?- d_sortedQfs(2, SQs), length(SQs, L).
%@    SQs = [[0/3,0/6],[0/3,1/6],[1/6,0/6],[0/6,2/6],[0/6,2/3],[1/6,1/6],[2/6,0/0],[2/3,0/0],[0/6,3/6],[0/6,3/3],[1/6,2/6],[1/6,2/3],[3/6,0/0],[3/3,0/0],[0/6,4/6],[1/6,3/6],[1/6,3/3],[2/6,2/6],[2/6,... / ...],[... / ...|...]|...], L = 29.

%?- d_sortedQfs(3, SQs), length(SQs, L).
%@    SQs = [[0/3,0/3,0/6],[0/3,0/3,1/6],[0/3,1/6,0/6],[1/6,0/3,0/6],[0/3,0/6,2/6],[0/3,0/6,2/3],[0/3,1/6,1/6],[1/6,0/3,1/6],[0/6,2/6,0/0],[0/6,2/3,0/0],[1/6,1/6,0/6],[2/6,0/0,0/0],[2/3,0/0,0/0],[0/3,0/6,3/6],[0/3,0/6,3/3],[0/3,1/6,2/6],[0/3,1/6,2/3],[1/6,0/6,... / ...],[1/6,... / ...|...],[... / ...|...]|...], L = 93.

%?- d_sortedQfs(4, SQs), length(SQs, L).
%@    SQs = [[0/3,0/3,0/3,0/6],[0/3,0/3,0/3,1/6],[0/3,0/3,1/6,0/6],[0/3,1/6,0/3,0/6],[1/6,0/3,0/3,0/6],[0/3,0/3,0/6,2/6],[0/3,0/3,0/6,2/3],[0/3,0/3,1/6,1/6],[0/3,1/6,0/3,1/6],[1/6,0/3,0/3,1/6],[0/3,0/6,2/6,0/0],[0/3,0/6,2/3,0/0],[0/3,1/6,1/6,0/6],[1/6,0/3,1/6,0/6],[0/6,2/6,0/0,0/0],[0/6,2/3,0/0,0/0],[1/6,1/6,0/3,... / ...],[2/6,0/0,... / ...|...],[2/3,... / ...|...],[... / ...|...]|...], L = 261.

% The guarantee I have regarding such a sorted Qf list is that,
% if I process its elements front-to-back, each next element
% cannot be below any of those previously processed.
% In particular, I do NOT have a guarantee that all minimal
% elements are contiguous in the front of the list!
% Nevertheless, this weaker guarantee is able to support
% an efficient stratification of the list into recursively
% peeled-off maximal sets.

sift(Q, [Bot|Higher], Strata) :-
    if_(tmember_t('≼'(Q), Bot),
        Strata = [[Q],Bot|Higher],
        sift_(Higher, Q, Bot, Strata)).

sift_([], Q, Bot, [[Q|Bot]]).
sift_([Next|More], Q, Bot, Strata) :-
    if_(tmember_t('≼'(Q), Next),
        Strata = [[Q|Bot],Next|More],
        (   Strata = [Bot|Strata1],
            sift_(More, Q, Next, Strata1)
        )
       ).

d_strata(D, Qss) :-
    d_sortedQfs(D, Qfs),
    foldl(sift, Qfs, [[]], RQss),
    reverse(RQss, Qss).

%?- S+\(d_strata(2, Qss), maplist(portray_clause, Qss), length(Qss, S)).
%@ [[0/6,2/6],[1/6,0/6],[0/3,0/6]].
%@ [[0/6,3/6],[1/6,1/6],[0/6,2/3],[0/3,1/6]].
%@ [[0/6,4/6],[1/6,2/6],[0/6,3/3],[2/6,0/0]].
%@ [[1/6,3/6],[1/6,2/3],[2/3,0/0]].
%@ [[1/6,4/6],[2/6,2/6],[1/6,3/3],[3/6,0/0]].
%@ [[2/6,3/6],[2/6,2/3],[3/3,0/0]].
%@ [[2/6,4/6],[3/6,2/6],[2/6,3/3],[4/6,0/0]].
%@ [[3/6,3/6],[3/6,2/3]].
%@ [[3/6,4/6],[3/6,3/3]].
%@    S = 9.

%?- S+\(d_strata(3, Qss), maplist(portray_clause, Qss), length(Qss, S)).
%@ [[0/6,2/6,2/6],[1/6,0/6,2/6],[1/6,1/6,0/6],[0/6,2/6,0/0],[0/3,0/6,2/6],[1/6,0/3,0/6],[0/3,1/6,0/6],[0/3,0/3,0/6]].
%@ [[0/6,2/6,3/6],[0/6,2/6,2/3],[1/6,0/6,3/6],[0/6,3/6,0/0],[1/6,1/6,1/6],[1/6,0/6,2/3],[0/3,0/6,3/6],[0/6,2/3,0/0],[1/6,0/3,1/6],[0/3,1/6,1/6],[0/3,0/6,2/3],[0/3,0/3,1/6]].
%@ [[0/6,2/6,4/6],[0/6,3/6,2/6],[0/6,2/6,3/3],[1/6,0/6,4/6],[0/6,4/6,0/0],[1/6,1/6,2/6],[1/6,0/6,3/3],[0/3,0/6,4/6],[1/6,2/6,0/0],[0/6,3/3,0/0],[0/3,1/6,2/6],[0/3,0/6,3/3],[2/6,0/0,0/0]].
%@ [[0/6,3/6,3/6],[0/6,3/6,2/3],[1/6,1/6,3/6],[1/6,1/6,2/3],[0/3,1/6,3/6],[1/6,2/3,0/0],[0/3,1/6,2/3],[2/3,0/0,0/0]].
%@ [[0/6,3/6,4/6],[0/6,3/6,3/3],[1/6,1/6,4/6],[1/6,2/6,2/6],[1/6,1/6,3/3],[0/3,1/6,4/6],[1/6,3/6,0/0],[0/3,1/6,3/3],[3/6,0/0,0/0]].
%@ [[1/6,2/6,3/6],[1/6,2/6,2/3],[2/6,2/6,0/0],[1/6,3/3,0/0],[3/3,0/0,0/0]].
%@ [[1/6,2/6,4/6],[1/6,3/6,2/6],[1/6,2/6,3/3],[1/6,4/6,0/0],[2/6,2/3,0/0]].
%@ [[1/6,3/6,3/6],[2/6,2/6,2/6],[1/6,3/6,2/3],[2/6,3/6,0/0],[4/6,0/0,0/0]].
%@ [[1/6,3/6,4/6],[2/6,2/6,3/6],[1/6,3/6,3/3],[2/6,2/6,2/3],[3/6,2/6,0/0],[2/6,3/3,0/0]].
%@ [[2/6,2/6,4/6],[2/6,3/6,2/6],[2/6,2/6,3/3],[2/6,4/6,0/0],[3/6,2/3,0/0]].
%@ [[2/6,3/6,3/6],[3/6,2/6,2/6],[2/6,3/6,2/3],[3/6,3/6,0/0]].
%@ [[2/6,3/6,4/6],[3/6,2/6,3/6],[2/6,3/6,3/3],[3/6,2/6,2/3],[3/6,3/3,0/0]].
%@ [[3/6,2/6,4/6],[3/6,3/6,2/6],[3/6,2/6,3/3],[3/6,4/6,0/0]].
%@ [[3/6,3/6,3/6],[3/6,3/6,2/3]].
%@ [[3/6,3/6,4/6],[3/6,3/6,3/3]].
%@    S = 15.

% Write out Hasse diagram as (GraphViz) DOT file.
d_writehassedot(D) :-
    phrase(format_("HasseD~d.dot", [D]), Filename),
    atom_chars(File, Filename),
    format("Opening file ~q...~n", [File]), % feedback to console
    setup_call_cleanup(open(File, write, OS),
		       (   format("Collecting final tallies ..", []),
                           % NB: We use _unrectified_ d_endtally_rec/3 to exhibit
                           %     the non-functoriality of default 3+3 dose recs.
                           findall(Q-X, d_endtally_rec(D,Q,X), QXs),
                           pairs_keys(QXs, Qs),
                           length(Qs, Nf),
                           format("~n sorting ~d final tallies ..", [Nf]),
                           qs_sorted(Qs, SQs),
                           format("~n stratifying ..~n", []),
                           foldl(sift, SQs, [[]], Qss),
                           reverse(Qss, RQss), maplist(portray_clause, RQss),
                           format(OS, "strict digraph hasseD~d {~n", [D]),
                           format(OS, "  rankdir=~a;~n", ['BT']),
                           format(OS, "  node [colorscheme=~w, fontname=\"~w\"];~n",
                                  ['set14','Helvetica:bold']),
                           format("Writing strata to DOT file ..", []),
                           list_to_assoc(QXs, QXassoc),
                           maplist(write_stratum(OS,QXassoc), Qss),
                           format("~n writing covering relation ..", []) ->
                           reverse(SQs, RSQs), % speeds cover calculation
                           time((   in_cover(RSQs, Q1, Q2),
			            format(OS, "  \"~w\" -> \"~w\";~n", [Q1,Q2]),
			            fail % exhaust all (Q1 -> Q2) arrows
			        ;   true
			        )),
                           format(OS, "}~n", [])
		       ),
		       close(OS)
		      ),
    format(".. done.~n", []).

write_stratum(OS, QXassoc, Qs) :-
    format(OS, "  { rank=same;~n", []),
    maplist(\Q^(get_assoc(Q, QXassoc, X), #Color #= #X + 1,
                format(OS, "    \"~w\" [fontcolor=~d];~n", [Q,Color])),
            Qs),
    format(OS, "  }~n", []).

%?- d_writehassedot(2).
%@ Opening file 'HasseD2.dot'...
%@ Collecting final tallies ..
%@  sorting 29 final tallies ..
%@  stratifying ..
%@ [[0/6,2/6],[1/6,0/6],[0/3,0/6]].
%@ [[0/6,3/6],[1/6,1/6],[0/6,2/3],[0/3,1/6]].
%@ [[0/6,4/6],[1/6,2/6],[0/6,3/3],[2/6,0/0]].
%@ [[1/6,3/6],[1/6,2/3],[2/3,0/0]].
%@ [[1/6,4/6],[2/6,2/6],[1/6,3/3],[3/6,0/0]].
%@ [[2/6,3/6],[2/6,2/3],[3/3,0/0]].
%@ [[2/6,4/6],[3/6,2/6],[2/6,3/3],[4/6,0/0]].
%@ [[3/6,3/6],[3/6,2/3]].
%@ [[3/6,4/6],[3/6,3/3]].
%@ Writing strata to DOT file ..
%@  writing covering relation ..   % CPU time: 5.718s, 28_403_617 inferences
%@ .. done.
%@    true.

%?- d_writehassedot(3).
%@ Opening file 'HasseD3.dot'...
%@ Collecting final tallies ..
%@  sorting 93 final tallies ..
%@  stratifying ..
%@ [[0/6,2/6,2/6],[1/6,0/6,2/6],[1/6,1/6,0/6],[0/6,2/6,0/0],[0/3,0/6,2/6],[1/6,0/3,0/6],[0/3,1/6,0/6],[0/3,0/3,0/6]].
%@ [[0/6,2/6,3/6],[0/6,2/6,2/3],[1/6,0/6,3/6],[0/6,3/6,0/0],[1/6,1/6,1/6],[1/6,0/6,2/3],[0/3,0/6,3/6],[0/6,2/3,0/0],[1/6,0/3,1/6],[0/3,1/6,1/6],[0/3,0/6,2/3],[0/3,0/3,1/6]].
%@ [[0/6,2/6,4/6],[0/6,3/6,2/6],[0/6,2/6,3/3],[1/6,0/6,4/6],[0/6,4/6,0/0],[1/6,1/6,2/6],[1/6,0/6,3/3],[0/3,0/6,4/6],[1/6,2/6,0/0],[0/6,3/3,0/0],[0/3,1/6,2/6],[0/3,0/6,3/3],[2/6,0/0,0/0]].
%@ [[0/6,3/6,3/6],[0/6,3/6,2/3],[1/6,1/6,3/6],[1/6,1/6,2/3],[0/3,1/6,3/6],[1/6,2/3,0/0],[0/3,1/6,2/3],[2/3,0/0,0/0]].
%@ [[0/6,3/6,4/6],[0/6,3/6,3/3],[1/6,1/6,4/6],[1/6,2/6,2/6],[1/6,1/6,3/3],[0/3,1/6,4/6],[1/6,3/6,0/0],[0/3,1/6,3/3],[3/6,0/0,0/0]].
%@ [[1/6,2/6,3/6],[1/6,2/6,2/3],[2/6,2/6,0/0],[1/6,3/3,0/0],[3/3,0/0,0/0]].
%@ [[1/6,2/6,4/6],[1/6,3/6,2/6],[1/6,2/6,3/3],[1/6,4/6,0/0],[2/6,2/3,0/0]].
%@ [[1/6,3/6,3/6],[2/6,2/6,2/6],[1/6,3/6,2/3],[2/6,3/6,0/0],[4/6,0/0,0/0]].
%@ [[1/6,3/6,4/6],[2/6,2/6,3/6],[1/6,3/6,3/3],[2/6,2/6,2/3],[3/6,2/6,0/0],[2/6,3/3,0/0]].
%@ [[2/6,2/6,4/6],[2/6,3/6,2/6],[2/6,2/6,3/3],[2/6,4/6,0/0],[3/6,2/3,0/0]].
%@ [[2/6,3/6,3/6],[3/6,2/6,2/6],[2/6,3/6,2/3],[3/6,3/6,0/0]].
%@ [[2/6,3/6,4/6],[3/6,2/6,3/6],[2/6,3/6,3/3],[3/6,2/6,2/3],[3/6,3/3,0/0]].
%@ [[3/6,2/6,4/6],[3/6,3/6,2/6],[3/6,2/6,3/3],[3/6,4/6,0/0]].
%@ [[3/6,3/6,3/6],[3/6,3/6,2/3]].
%@ [[3/6,3/6,4/6],[3/6,3/6,3/3]].
%@ Writing strata to DOT file ..
%@  writing covering relation ..   % CPU time: 121.519s, 612_386_652 inferences
%@ .. done.
%@    true.

%?- Q1^Q2+\(findall(Q, d_mendtally_rec(2,Q,_), Qfs), in_cover(Qfs, Q1, Q2)).
%@    Q1 = [0/3,1/6], Q2 = [0/3,0/6]
%@ ;  Q1 = [0/6,2/3], Q2 = [0/6,2/6]
%@ ;  Q1 = [0/6,3/3], Q2 = [0/6,2/3]
%@ ;  Q1 = [0/6,3/3], Q2 = [0/6,3/6]
%@ ;  Q1 = [0/6,3/6], Q2 = [0/6,2/6]
%@ ;  Q1 = [0/6,4/6], Q2 = [0/6,3/6]
%@ ;  Q1 = [1/6,1/6], Q2 = [0/6,2/6]
%@ ;  Q1 = [1/6,1/6], Q2 = [1/6,0/6]
%@ ;  Q1 = [1/6,2/3], Q2 = [0/6,3/3]
%@ ;  Q1 = [1/6,2/3], Q2 = [1/6,2/6]
%@ ;  Q1 = [1/6,2/6], Q2 = [0/6,3/6]
%@ ;  Q1 = [1/6,2/6], Q2 = [1/6,1/6]
%@ ;  Q1 = [1/6,3/3], Q2 = [1/6,2/3]
%@ ;  Q1 = [1/6,3/3], Q2 = [1/6,3/6]
%@ ;  Q1 = [1/6,3/6], Q2 = [0/6,4/6]
%@ ;  Q1 = [1/6,3/6], Q2 = [1/6,2/6]
%@ ;  Q1 = [1/6,4/6], Q2 = [0/6,2/3]
%@ ;  Q1 = [1/6,4/6], Q2 = [1/6,3/6]
%@ ;  Q1 = [2/3,0/0], Q2 = [0/3,1/6]
%@ ;  Q1 = [2/3,0/0], Q2 = [2/6,0/0]
%@ ;  Q1 = [2/6,0/0], Q2 = [0/6,2/3]
%@ ;  Q1 = [2/6,0/0], Q2 = [1/6,1/6]
%@ ;  Q1 = [2/6,2/3], Q2 = [1/6,3/3]
%@ ;  Q1 = [2/6,2/3], Q2 = [2/6,2/6]
%@ ;  Q1 = [2/6,2/6], Q2 = [1/6,3/6]
%@ ;  Q1 = [2/6,3/3], Q2 = [2/6,0/0]
%@ ;  Q1 = [2/6,3/3], Q2 = [2/6,2/3]
%@ ;  Q1 = [2/6,3/3], Q2 = [2/6,3/6]
%@ ;  Q1 = [2/6,3/6], Q2 = [1/6,4/6]
%@ ;  Q1 = [2/6,3/6], Q2 = [2/6,2/6]
%@ ;  Q1 = [2/6,4/6], Q2 = [1/6,2/3]
%@ ;  Q1 = [2/6,4/6], Q2 = [2/6,3/6]
%@ ;  Q1 = [3/3,0/0], Q2 = [2/3,0/0]
%@ ;  Q1 = [3/3,0/0], Q2 = [3/6,0/0]
%@ ;  Q1 = [3/6,0/0], Q2 = [0/3,1/6]
%@ ;  Q1 = [3/6,0/0], Q2 = [1/6,2/3]
%@ ;  Q1 = [3/6,0/0], Q2 = [2/6,0/0]
%@ ;  Q1 = [3/6,2/3], Q2 = [2/6,3/3]
%@ ;  Q1 = [3/6,2/3], Q2 = [3/6,2/6]
%@ ;  Q1 = [3/6,2/6], Q2 = [0/3,1/6]
%@ ;  Q1 = [3/6,2/6], Q2 = [2/6,3/6]
%@ ;  Q1 = [3/6,3/3], Q2 = [3/6,0/0]
%@ ;  Q1 = [3/6,3/3], Q2 = [3/6,2/3]
%@ ;  Q1 = [3/6,3/3], Q2 = [3/6,3/6]
%@ ;  Q1 = [3/6,3/6], Q2 = [2/6,4/6]
%@ ;  Q1 = [3/6,3/6], Q2 = [3/6,2/6]
%@ ;  Q1 = [3/6,4/6], Q2 = [2/6,2/3]
%@ ;  Q1 = [3/6,4/6], Q2 = [3/6,3/6]
%@ ;  Q1 = [4/6,0/0], Q2 = [2/6,2/3]
%@ ;  Q1 = [4/6,0/0], Q2 = [3/6,0/0]
%@ ;  false. % Covering relation in 𝒬f (D=2 case) has just 50 pairs.

/*
We now seek the parameters (g₀, g₁, g₂) of a lower-Galois enrollment for D=2,
as defined in Eq (15).

  F(q) ≤ x ⟹ q ≼ gₓ  ∀ q ∈ 𝒬f, 0 ≤ x ≤ D.

We are looking also for *minimal* such values of the gₓ ∈ 𝒬.
*/

% Generate the several relevant subsets of 𝒬f
% TODO: Keeping in mind that we are calculating F⁻¹(Xrange),
%       there could be some value to a left-to-right naming
%       such as d_rec_Finv/3.
d_qfs_rec(D, Qfs, Xrange) :-
    findall(Qf, (d_mendtally_rec(D, Qf, X), X in Xrange), Qfs).

%?- d_qfs_rec(2, Q0s, 0), length(Q0s, L0).
%@    Q0s = [[2/3,0/0],[2/6,0/0],[2/6,2/3],[2/6,2/6],[2/6,3/3],[2/6,3/6],[2/6,4/6],[3/3,0/0],[3/6,0/0],[3/6,2/3],[3/6,2/6],[3/6,3/3],[3/6,3/6],[3/6,4/6],[4/6,0/0]], L0 = 15.

%?- d_qfs_rec(2, Q12s, 1..2), length(Q12s, L12).
%@    Q12s = [[0/3,0/6],[0/3,1/6],[0/6,2/3],[0/6,2/6],[0/6,3/3],[0/6,3/6],[0/6,4/6],[1/6,0/6],[1/6,1/6],[1/6,2/3],[1/6,2/6],[1/6,3/3],[1/6,3/6],[1/6,4/6]], L12 = 14.

% Construct maximal and minimal subsets
% TODO: Eliminate duplicated code by taking relation as parameter.
qs_maxs([], []).
qs_maxs([Q|Qs], Maxs) :-
    tpartition('≽'(Q), Qs, _, Qs1),
    if_(tmember_t('≼'(Q), Qs1), % ∃ Q' ∈ Qs s.t. Q ≼ Q' ?
        qs_maxs(Qs1, Maxs), % if so, Q is not maximal
        (   Maxs = [Q|Maxs1], % otherwise, it is
            qs_maxs(Qs1, Maxs1)
        )
       ).

qs_mins([], []).
qs_mins([Q|Qs], Mins) :-
    tpartition('≼'(Q), Qs, _, Qs1),
    if_(tmember_t('≽'(Q), Qs1), % ∃ Q' ∈ Qs s.t. Q' ≼ Q ?
        qs_mins(Qs1, Mins), % if so, Q is not minimal
        (   Mins = [Q|Mins1], % otherwise, it is
            qs_mins(Qs1, Mins1)
        )
       ).

% Regions near the origin
% TODO: Find a name conveying geometrical intutition ('sphere'? 'hypercube'?),
%       or perhaps link this to *accessible* tallies as discussed in Fact 1.27.
% TODO: Also deal with the 'qs' plurality; perhaps in this module, a given tally
%       counts as 'q', and only _lists_ of tallies should be regarded a plural?
qs_d_nmax(Qs, D, Nmax) :-
    length(Qs, D),
    maplist(\Q^T^N^(Q = T/N), Qs, Ts, Ns),
    Ns ins 0..Nmax, label(Ns),
    maplist(\T^N^(T in 0..N), Ts, Ns), label(Ts).

d_gs_rec(D, Gs, X, Nmax) :-
    X in 0..D, indomain(X),
    % Calculate Qls = F⁻¹(0..X)
    findall(Qf, (d_endtally_rec(D, Qf, Xi), Xi in 0..X), Qls),
    qs_maxs(Qls, Qls1), % q ∈ Qls ⟹ ∃ q' ∈ Qls1 . q ≼ q'
    % Having calculated the maximal elements of F⁻¹(0..X),
    % we now proceed to search for all candidate gₓ's.
    findall(C, (qs_d_nmax(C, D, Nmax),
                maplist('≽'(C), Qls1)), Cs),
    qs_mins(Cs, Gs).

d_gs_rec(D, Gs, X) :- d_gs_rec(D, Gs, X, 6).

%?- time(d_gs_rec(2, Gs, X)).
%@    % CPU time: 1.199s, 5_774_900 inferences
%@    Gs = [[2/6,0/4]], X = 0
%@ ;  % CPU time: 0.840s, 4_052_245 inferences
%@    Gs = [[0/6,2/6]], X = 1
%@ ;  % CPU time: 0.880s, 4_241_926 inferences
%@    Gs = [[0/6,0/5]], X = 2.

%?- time(d_gs_rec(3, Gs, X)).
%@    % CPU time: 39.542s, 194_608_812 inferences
%@    Gs = [[2/6,0/4,0/4]], X = 0
%@ ;  % CPU time: 29.026s, 144_788_174 inferences
%@    Gs = [[0/6,2/6,0/4]], X = 1
%@ ;  % CPU time: 28.822s, 143_985_181 inferences
%@    Gs = [[0/6,0/5,2/6]], X = 2
%@ ;  % CPU time: 29.160s, 145_735_273 inferences
%@    Gs = [[0/6,0/5,0/5]], X = 3.

%?- [2/6,0/4,0/4] '≼' [0/6,2/6,0/4].
%@    true.

%?- time(d_gs_rec(4, Gs, X)).
%@    % CPU time: 1146.519s, 5_745_737_901 inferences
%@    Gs = [[2/6,0/4,0/4,0/4]], X = 0
%@ ;  % CPU time: 977.587s, 4_976_964_589 inferences
%@    Gs = [[0/6,2/6,0/4,0/4]], X = 1
%@ ;  % CPU time: 959.801s, 4_916_987_366 inferences
%@    Gs = [[0/6,0/5,2/6,0/4]], X = 2
%@ ;  % CPU time: 962.464s, 4_905_704_908 inferences
%@    Gs = [[0/6,0/5,0/5,2/6]], X = 3
%@ ;  % CPU time: 954.726s, 4_907_056_586 inferences
%@    Gs = [[0/6,0/5,0/5,0/5]], X = 4.

/*
From the above, we see that (as expected) a separate 'rectification'
step is not truly needed, and that the calculation of candidate g's
automatically ensures functoriality of the resulting lower-Galois
enrollment.

That represents progress toward simplification, but (apparently)
not toward improved time-complexity, nor even a substantial speedup.

One thing we might do, however, is to incorporate the minimization
into the search itself.  If we already have a non-empty set of
valid gₓ's that are minimal among those found thus far, then any
new g' that we might like to test can be rejected immediately if
it exceeds *any* element of this set.  Such quick rejection will
avoid costly checking against _all_ of the Qls1.

What if I were scanning a *sorted* list of all admissible tallies?
Would I enjoy any guarantee that allowed me to cut short my scan
at any point?  How might I know that I won't find any additional
minimal gₓ's for some given x?

Suppose I search a list sorted low-to-high along -≼-> arrows,
and find a valid gₓ that is however not minimal relative to the
gₓ's I've already found.  Could this guarantee I will never find
another minimal gₓ further along (higher up) the list?  I think
that's too much to hope for.

But what about the question of minimality?  Because I can never
find a later element in the list that is _below_ a previously
seen element (including any gₓ's collected thus far), I do know
that none of the gₓ's already proven minimal could possibly get
knocked out by a new one.  So the only question I need to ask
under these circumstances is whether any of the previously
collected gₓ's is below g'.  If so, then g' can be ignored.

Perhaps this means rather that I should switch to finding gₓ₊₁?
That is, I may now have a scheme for processing the hypercube
in a single pass.
*/

% Today, let's see how much we can speed this up by such a
% single-pass processing of a sorted hypercube.
% This really starts to look like a job for a DCG!
% But perhaps a foldl/4 is more clearly in order.
% I will need a suitable _accumulator_ for this.
% Accumulator at any time knows the full list of (D+1)
% maximal strata which the gₓ's must sit above.
% Accumulator also knows for which X it is currently
% seeking a gₓ.  (It may rather make sense for accumulator
% to hold only current and yet-unprocessed strata.)
% Since my aim here is to explore *potential* speedups,
% I could even treat first gₓ I find for each X as *the*
% minimal one!  That is, I am announcing from the outset
% that I will seek only single representatives of what may
% generally (unless some theorem holds to the contrary!)
% be non-singleton gₓ lists of options for some X's.

% Aha!  I realized on my walk this morning (10/18) that the
% fact 𝒬 is a _lattice_ guarantees that each gₓ is unique!
% This changes everything.  It allows me to search an
% ascending list of the hypercube, taking the *first*
% 'candidate' gₓ (for each x) as _the_ unique value.
% The search can then increment x and find the next g.

% I think actually a foldl/4 may not allow fully for the
% efficiencies possible here, and that a 'monolithic'
% recursion may better solve the problem.

% Interestingly, I now seem to have found a use for '⋡'/3 below!
'⋡'(Q1s, Q2s, Truth) :- '≽'(Q1s, Q2s, Untruth),
                        reif:non(Untruth, Truth).

% Here, galois/4 is searching [Q|Qs] for the first Gx
% satisfying Q ≼ Gx ∀ Q ∈ Ms, or equivalently ↓Gx ⊇ Ms.
% It has already found Gs0, and 
galois([Ms|Mss], [Q|Qs], Gs0, Gs) :-
    % If Q is not above _any_ of the Ms, then skip it;
    % otherwise (Q is above *all* Ms), prepend to Gs and recurse.
    if_(tmember_t('⋡'(Q), Ms), % ∃ M ∈ Ms s.t. M ⋠ Q ?
        galois([Ms|Mss], Qs, Gs0, Gs), % if so, Q is not a Gx;
        (   format("↓~w ⊇ ~w.~n", [Q, Ms]),
            Gs1 = [Q|Gs0],
            length(Qs, LQ),
            format("Mss = ~w, |Qs| = ~d, Gs1 = ~w.~n", [Mss, LQ, Gs1]),
            galois(Mss, Qs, Gs1, Gs) % otherwise, we collect it and recurse
        )
       ).
galois([], _, Gs, Gs). % Succeed when all strata are accounted-for.

d_gs(D, Gs) :-
    format("Listing Qs...... ", []),
    time(findall(Q, qs_d_nmax(Q, D, 6), Qs)),
    format("Sorting Qs...... ", []),
    time(qs_sorted(Qs, SQs)),
    format("Reversing....... ", []),
    time(reverse(SQs, RQs)),
    format("Stratifying Qf.. ", []),
    time(d_Qfstratamax(D, Mss)),
    format("Finding g's ..~n", []),
    time(galois(Mss, RQs, [], RGs)),
    reverse(RGs, Gs).

%?- time(d_gs(4, Gs)). % Perhaps this is feasible _now_?
%@ Listing Qs......    % CPU time: 43.456s, 182_781_614 inferences
%@ Sorting Qs...... Encoding Qs...    % CPU time: 679.046s, 3_594_977_411 inferences
%@ Sorting Qs....    % CPU time: 0.632s, 2 inferences
%@ Sizing Qs.....    % CPU time: 0.648s, 6_146_561 inferences
%@ Decoding......    % CPU time: 1187.057s, 7_752_694_545 inferences
%@    % CPU time: 1867.513s, 11_355_055_949 inferences
%@ Reversing.......    % CPU time: 0.280s, 614_658 inferences
%@ Stratifying Qf..    % CPU time: 12.384s, 57_444_988 inferences
%@ Finding g's ..

%?- time(d_gs(3, Gs)). % After #'ing everything in q_r/2
%@ Listing Qs......    % CPU time: 1.588s, 6_660_460 inferences
%@ Sorting Qs...... Encoding Qs...    % CPU time: 20.434s, 109_988_099 inferences
%@ Sorting Qs....    % CPU time: 0.017s, 2 inferences
%@ Sizing Qs.....    % CPU time: 0.019s, 175_617 inferences
%@ Decoding......    % CPU time: 31.490s, 207_539_697 inferences
%@    % CPU time: 51.972s, 317_755_335 inferences
%@ Reversing.......    % CPU time: 0.005s, 21_954 inferences
%@ Stratifying Qf..    % CPU time: 3.393s, 15_670_513 inferences
%@ Finding g's ..
%@ ↓[2/6,0/4,0/4] ⊇ [[2/6,0/0,0/0],[2/6,2/6,0/0],[2/6,2/6,2/6]].
%@ Mss = [[[0/6,2/6,0/0],[0/6,2/6,2/6]],[[0/3,0/6,2/6],[1/6,0/6,2/6]],[[0/3,0/3,0/6],[0/3,1/6,0/6],[1/6,0/3,0/6],[1/6,1/6,0/6]]], |Qs| = 2494, Gs1 = [[2/6,0/4,0/4]].
%@ ↓[0/6,2/6,0/4] ⊇ [[0/6,2/6,0/0],[0/6,2/6,2/6]].
%@ Mss = [[[0/3,0/6,2/6],[1/6,0/6,2/6]],[[0/3,0/3,0/6],[0/3,1/6,0/6],[1/6,0/3,0/6],[1/6,1/6,0/6]]], |Qs| = 1978, Gs1 = [[0/6,2/6,0/4],[2/6,0/4,0/4]].
%@ ↓[0/5,0/6,2/6] ⊇ [[0/3,0/6,2/6],[1/6,0/6,2/6]].
%@ Mss = [[[0/3,0/3,0/6],[0/3,1/6,0/6],[1/6,0/3,0/6],[1/6,1/6,0/6]]], |Qs| = 1228, Gs1 = [[0/5,0/6,2/6],[0/6,2/6,0/4],[2/6,0/4,0/4]].
%@ ↓[0/5,0/5,0/6] ⊇ [[0/3,0/3,0/6],[0/3,1/6,0/6],[1/6,0/3,0/6],[1/6,1/6,0/6]].
%@ Mss = [], |Qs| = 8, Gs1 = [[0/5,0/5,0/6],[0/5,0/6,2/6],[0/6,2/6,0/4],[2/6,0/4,0/4]].
%@    % CPU time: 29.991s, 153_168_191 inferences
%@    % CPU time: 86.957s, 493_286_608 inferences
%@    Gs = [[2/6,0/4,0/4],[0/6,2/6,0/4],[0/5,0/6,2/6],[0/5,0/5,0/6]].

%?- time(d_gs(3, Gs)). % After #'ing stuff in d_int_kt_ku/4
%@ Listing Qs......    % CPU time: 1.610s, 6_660_460 inferences
%@ Sorting Qs...... Encoding Qs...    % CPU time: 19.827s, 106_168_451 inferences
%@ Sorting Qs....    % CPU time: 0.018s, 2 inferences
%@ Sizing Qs.....    % CPU time: 0.020s, 175_617 inferences
%@ Decoding......    % CPU time: 38.164s, 245_604_465 inferences
%@    % CPU time: 58.040s, 352_000_455 inferences
%@ Reversing.......    % CPU time: 0.006s, 21_954 inferences
%@ Stratifying Qf..    % CPU time: 3.358s, 15_549_757 inferences
%@ Finding g's ..
%@ ↓[2/6,0/4,0/4] ⊇ [[2/6,0/0,0/0],[2/6,2/6,0/0],[2/6,2/6,2/6]].
%@ Mss = [[[0/6,2/6,0/0],[0/6,2/6,2/6]],[[0/3,0/6,2/6],[1/6,0/6,2/6]],[[0/3,0/3,0/6],[0/3,1/6,0/6],[1/6,0/3,0/6],[1/6,1/6,0/6]]], |Qs| = 2494, Gs1 = [[2/6,0/4,0/4]].
%@ ↓[0/6,2/6,0/4] ⊇ [[0/6,2/6,0/0],[0/6,2/6,2/6]].
%@ Mss = [[[0/3,0/6,2/6],[1/6,0/6,2/6]],[[0/3,0/3,0/6],[0/3,1/6,0/6],[1/6,0/3,0/6],[1/6,1/6,0/6]]], |Qs| = 1978, Gs1 = [[0/6,2/6,0/4],[2/6,0/4,0/4]].
%@ ↓[0/5,0/6,2/6] ⊇ [[0/3,0/6,2/6],[1/6,0/6,2/6]].
%@ Mss = [[[0/3,0/3,0/6],[0/3,1/6,0/6],[1/6,0/3,0/6],[1/6,1/6,0/6]]], |Qs| = 1228, Gs1 = [[0/5,0/6,2/6],[0/6,2/6,0/4],[2/6,0/4,0/4]].
%@ ↓[0/5,0/5,0/6] ⊇ [[0/3,0/3,0/6],[0/3,1/6,0/6],[1/6,0/3,0/6],[1/6,1/6,0/6]].
%@ Mss = [], |Qs| = 8, Gs1 = [[0/5,0/5,0/6],[0/5,0/6,2/6],[0/6,2/6,0/4],[2/6,0/4,0/4]].
%@    % CPU time: 28.801s, 145_469_735 inferences
%@    % CPU time: 91.824s, 519_712_516 inferences
%@    Gs = [[2/6,0/4,0/4],[0/6,2/6,0/4],[0/5,0/6,2/6],[0/5,0/5,0/6]].

%?- time(d_gs(3, Gs)). % After precomputing d_maxenc/2
%@ Listing Qs......    % CPU time: 1.603s, 6_660_460 inferences
%@ Sorting Qs...... Encoding Qs...    % CPU time: 20.060s, 106_168_451 inferences
%@ Sorting Qs....    % CPU time: 0.017s, 2 inferences
%@ Sizing Qs.....    % CPU time: 0.019s, 175_617 inferences
%@ Decoding......    % CPU time: 45.324s, 286_742_507 inferences
%@    % CPU time: 65.432s, 393_138_497 inferences
%@ Reversing.......    % CPU time: 0.006s, 21_954 inferences
%@ Stratifying Qf..    % CPU time: 3.404s, 15_549_757 inferences
%@ Finding g's ..
%@ ↓[2/6,0/4,0/4] ⊇ [[2/6,0/0,0/0],[2/6,2/6,0/0],[2/6,2/6,2/6]].
%@ Mss = [[[0/6,2/6,0/0],[0/6,2/6,2/6]],[[0/3,0/6,2/6],[1/6,0/6,2/6]],[[0/3,0/3,0/6],[0/3,1/6,0/6],[1/6,0/3,0/6],[1/6,1/6,0/6]]], |Qs| = 2494, Gs1 = [[2/6,0/4,0/4]].
%@ ↓[0/6,2/6,0/4] ⊇ [[0/6,2/6,0/0],[0/6,2/6,2/6]].
%@ Mss = [[[0/3,0/6,2/6],[1/6,0/6,2/6]],[[0/3,0/3,0/6],[0/3,1/6,0/6],[1/6,0/3,0/6],[1/6,1/6,0/6]]], |Qs| = 1978, Gs1 = [[0/6,2/6,0/4],[2/6,0/4,0/4]].
%@ ↓[0/5,0/6,2/6] ⊇ [[0/3,0/6,2/6],[1/6,0/6,2/6]].
%@ Mss = [[[0/3,0/3,0/6],[0/3,1/6,0/6],[1/6,0/3,0/6],[1/6,1/6,0/6]]], |Qs| = 1228, Gs1 = [[0/5,0/6,2/6],[0/6,2/6,0/4],[2/6,0/4,0/4]].
%@ ↓[0/5,0/5,0/6] ⊇ [[0/3,0/3,0/6],[0/3,1/6,0/6],[1/6,0/3,0/6],[1/6,1/6,0/6]].
%@ Mss = [], |Qs| = 8, Gs1 = [[0/5,0/5,0/6],[0/5,0/6,2/6],[0/6,2/6,0/4],[2/6,0/4,0/4]].
%@    % CPU time: 29.085s, 145_469_735 inferences
%@    % CPU time: 99.538s, 560_850_558 inferences
%@    Gs = [[2/6,0/4,0/4],[0/6,2/6,0/4],[0/5,0/6,2/6],[0/5,0/5,0/6]].
%@ Listing Qs......    % CPU time: 1.613s, 6_660_460 inferences
%@ Sorting Qs...... Encoding Qs...    % CPU time: 22.714s, 121_049_849 inferences
%@ Sorting Qs....    % CPU time: 0.019s, 2 inferences
%@ Sizing Qs.....    % CPU time: 0.019s, 175_617 inferences
%@ Decoding......    % CPU time: 47.516s, 299_452_715 inferences
%@    % CPU time: 70.279s, 420_730_103 inferences
%@ Reversing.......    % CPU time: 0.005s, 21_954 inferences
%@ Stratifying Qf..    % CPU time: 3.404s, 15_549_757 inferences
%@ Finding g's ..
%@ ↓[2/6,0/4,0/4] ⊇ [[2/6,0/0,0/0],[2/6,2/6,0/0],[2/6,2/6,2/6]].
%@ Mss = [[[0/6,2/6,0/0],[0/6,2/6,2/6]],[[0/3,0/6,2/6],[1/6,0/6,2/6]],[[0/3,0/3,0/6],[0/3,1/6,0/6],[1/6,0/3,0/6],[1/6,1/6,0/6]]], |Qs| = 2494, Gs1 = [[2/6,0/4,0/4]].
%@ ↓[0/6,2/6,0/4] ⊇ [[0/6,2/6,0/0],[0/6,2/6,2/6]].
%@ Mss = [[[0/3,0/6,2/6],[1/6,0/6,2/6]],[[0/3,0/3,0/6],[0/3,1/6,0/6],[1/6,0/3,0/6],[1/6,1/6,0/6]]], |Qs| = 1978, Gs1 = [[0/6,2/6,0/4],[2/6,0/4,0/4]].
%@ ↓[0/5,0/6,2/6] ⊇ [[0/3,0/6,2/6],[1/6,0/6,2/6]].
%@ Mss = [[[0/3,0/3,0/6],[0/3,1/6,0/6],[1/6,0/3,0/6],[1/6,1/6,0/6]]], |Qs| = 1228, Gs1 = [[0/5,0/6,2/6],[0/6,2/6,0/4],[2/6,0/4,0/4]].
%@ ↓[0/5,0/5,0/6] ⊇ [[0/3,0/3,0/6],[0/3,1/6,0/6],[1/6,0/3,0/6],[1/6,1/6,0/6]].
%@ Mss = [], |Qs| = 8, Gs1 = [[0/5,0/5,0/6],[0/5,0/6,2/6],[0/6,2/6,0/4],[2/6,0/4,0/4]].
%@    % CPU time: 29.068s, 145_469_735 inferences
%@    % CPU time: 104.378s, 588_442_164 inferences
%@    Gs = [[2/6,0/4,0/4],[0/6,2/6,0/4],[0/5,0/6,2/6],[0/5,0/5,0/6]].

%?- time(d_gs(4, Gs)). % Has this become feasible? (ALMOST!)
%@ Listing Qs......    % CPU time: 43.552s, 182_781_614 inferences
%@ Sorting Qs...... Encoding Qs...    % CPU time: 875.273s, 4_738_223_165 inferences
%@ Sorting Qs....    % CPU time: 0.638s, 2 inferences
%@ Sizing Qs.....    % CPU time: 0.643s, 6_146_561 inferences
%@ Decoding......    % CPU time: 185.771s, 1_177_910_766 inferences
% < interrupted during decoding, as %MEM had hit 65% and still growing >
%@    % CPU time: 1066.593s, 5_923_517_910 inferences
%@    % CPU time: 1110.149s, 6_106_303_711 inferences
%@    error('$interrupt_thrown',repl/0).

%?- time(d_gs(3, Gs)). % After precomputing placevalues/1
%@ Listing Qs......    % CPU time: 1.566s, 6_660_460 inferences
%@ Sorting Qs...... Encoding Qs...    % CPU time: 27.714s, 151_958_265 inferences
%@ Sorting Qs....    % CPU time: 0.017s, 2 inferences
%@ Sizing Qs.....    % CPU time: 0.019s, 175_617 inferences
%@ Decoding......    % CPU time: 49.405s, 314_906_923 inferences
%@    % CPU time: 77.167s, 467_092_727 inferences
%@ Reversing.......    % CPU time: 0.006s, 21_954 inferences
%@ Stratifying Qf..    % CPU time: 3.343s, 15_549_757 inferences
%@ Finding g's ..
%@ ↓[2/6,0/4,0/4] ⊇ [[2/6,0/0,0/0],[2/6,2/6,0/0],[2/6,2/6,2/6]].
%@ Mss = [[[0/6,2/6,0/0],[0/6,2/6,2/6]],[[0/3,0/6,2/6],[1/6,0/6,2/6]],[[0/3,0/3,0/6],[0/3,1/6,0/6],[1/6,0/3,0/6],[1/6,1/6,0/6]]], |Qs| = 2494, Gs1 = [[2/6,0/4,0/4]].
%@ ↓[0/6,2/6,0/4] ⊇ [[0/6,2/6,0/0],[0/6,2/6,2/6]].
%@ Mss = [[[0/3,0/6,2/6],[1/6,0/6,2/6]],[[0/3,0/3,0/6],[0/3,1/6,0/6],[1/6,0/3,0/6],[1/6,1/6,0/6]]], |Qs| = 1978, Gs1 = [[0/6,2/6,0/4],[2/6,0/4,0/4]].
%@ ↓[0/5,0/6,2/6] ⊇ [[0/3,0/6,2/6],[1/6,0/6,2/6]].
%@ Mss = [[[0/3,0/3,0/6],[0/3,1/6,0/6],[1/6,0/3,0/6],[1/6,1/6,0/6]]], |Qs| = 1228, Gs1 = [[0/5,0/6,2/6],[0/6,2/6,0/4],[2/6,0/4,0/4]].
%@ ↓[0/5,0/5,0/6] ⊇ [[0/3,0/3,0/6],[0/3,1/6,0/6],[1/6,0/3,0/6],[1/6,1/6,0/6]].
%@ Mss = [], |Qs| = 8, Gs1 = [[0/5,0/5,0/6],[0/5,0/6,2/6],[0/6,2/6,0/4],[2/6,0/4,0/4]].
%@    % CPU time: 28.593s, 145_469_735 inferences
%@    % CPU time: 110.684s, 634_804_811 inferences
%@    Gs = [[2/6,0/4,0/4],[0/6,2/6,0/4],[0/5,0/6,2/6],[0/5,0/5,0/6]].

%?- time(d_gs(3, Gs)).
%@ Listing Qs......    % CPU time: 1.638s, 6_660_460 inferences
%@ Sorting Qs......    % CPU time: 192.997s, 1_019_331_176 inferences
%@ Reversing.......    % CPU time: 0.006s, 21_954 inferences
%@ Stratifying Qf..    % CPU time: 3.434s, 15_549_757 inferences
%@ Finding g's ..
%@ ↓[2/6,0/4,0/4] ⊇ [[2/6,0/0,0/0],[2/6,2/6,0/0],[2/6,2/6,2/6]].
%@ Mss = [[[0/6,2/6,0/0],[0/6,2/6,2/6]],[[0/3,0/6,2/6],[1/6,0/6,2/6]],[[0/3,0/3,0/6],[0/3,1/6,0/6],[1/6,0/3,0/6],[1/6,1/6,0/6]]], |Qs| = 2494, Gs1 = [[2/6,0/4,0/4]].
%@ ↓[0/6,2/6,0/4] ⊇ [[0/6,2/6,0/0],[0/6,2/6,2/6]].
%@ Mss = [[[0/3,0/6,2/6],[1/6,0/6,2/6]],[[0/3,0/3,0/6],[0/3,1/6,0/6],[1/6,0/3,0/6],[1/6,1/6,0/6]]], |Qs| = 1978, Gs1 = [[0/6,2/6,0/4],[2/6,0/4,0/4]].
%@ ↓[0/5,0/6,2/6] ⊇ [[0/3,0/6,2/6],[1/6,0/6,2/6]].
%@ Mss = [[[0/3,0/3,0/6],[0/3,1/6,0/6],[1/6,0/3,0/6],[1/6,1/6,0/6]]], |Qs| = 1228, Gs1 = [[0/5,0/6,2/6],[0/6,2/6,0/4],[2/6,0/4,0/4]].
%@ ↓[0/5,0/5,0/6] ⊇ [[0/3,0/3,0/6],[0/3,1/6,0/6],[1/6,0/3,0/6],[1/6,1/6,0/6]].
%@ Mss = [], |Qs| = 8, Gs1 = [[0/5,0/5,0/6],[0/5,0/6,2/6],[0/6,2/6,0/4],[2/6,0/4,0/4]].
%@    % CPU time: 35.667s, 145_469_735 inferences
%@    % CPU time: 233.751s, 1_187_043_271 inferences
%@    Gs = [[2/6,0/4,0/4],[0/6,2/6,0/4],[0/5,0/6,2/6],[0/5,0/5,0/6]].

%?- Pct is 100*193/234.
%@    Pct = 82.47863247863248. % 0.8 of the time is spent in qs_sorted/2!

%?- time(d_gs(2, Gs)).
%@ ↓[2/6,0/4] ⊇ [[2/6,0/0],[2/6,2/6]].
%@ Mss = [[[0/6,2/6]],[[0/3,0/6],[1/6,0/6]]], |Qs| = 207, Gs1 = [[2/6,0/4]].
%@ ↓[0/6,2/6] ⊇ [[0/6,2/6]].
%@ Mss = [[[0/3,0/6],[1/6,0/6]]], |Qs| = 133, Gs1 = [[0/6,2/6],[2/6,0/4]].
%@ ↓[0/5,0/6] ⊇ [[0/3,0/6],[1/6,0/6]].
%@ Mss = [], |Qs| = 2, Gs1 = [[0/5,0/6],[0/6,2/6],[2/6,0/4]].
%@    % CPU time: 5.865s, 32_171_678 inferences
%@    Gs = [[2/6,0/4],[0/6,2/6],[0/5,0/6]].

%?- time(d_gs(3, Gs)).
%@ ↓[2/6,0/4,0/4] ⊇ [[2/6,0/0,0/0],[2/6,2/6,0/0],[2/6,2/6,2/6]].
%@ Mss = [[[0/6,2/6,0/0],[0/6,2/6,2/6]],[[0/3,0/6,2/6],[1/6,0/6,2/6]],[[0/3,0/3,0/6],[0/3,1/6,0/6],[1/6,0/3,0/6],[1/6,1/6,0/6]]], |Qs| = 2494, Gs1 = [[2/6,0/4,0/4]].
%@ ↓[0/6,2/6,0/4] ⊇ [[0/6,2/6,0/0],[0/6,2/6,2/6]].
%@ Mss = [[[0/3,0/6,2/6],[1/6,0/6,2/6]],[[0/3,0/3,0/6],[0/3,1/6,0/6],[1/6,0/3,0/6],[1/6,1/6,0/6]]], |Qs| = 1978, Gs1 = [[0/6,2/6,0/4],[2/6,0/4,0/4]].
%@ ↓[0/5,0/6,2/6] ⊇ [[0/3,0/6,2/6],[1/6,0/6,2/6]].
%@ Mss = [[[0/3,0/3,0/6],[0/3,1/6,0/6],[1/6,0/3,0/6],[1/6,1/6,0/6]]], |Qs| = 1228, Gs1 = [[0/5,0/6,2/6],[0/6,2/6,0/4],[2/6,0/4,0/4]].
%@ ↓[0/5,0/5,0/6] ⊇ [[0/3,0/3,0/6],[0/3,1/6,0/6],[1/6,0/3,0/6],[1/6,1/6,0/6]].
%@ Mss = [], |Qs| = 8, Gs1 = [[0/5,0/5,0/6],[0/5,0/6,2/6],[0/6,2/6,0/4],[2/6,0/4,0/4]].
%@    % CPU time: 213.793s, 1_187_033_066 inferences
%@    Gs = [[2/6,0/4,0/4],[0/6,2/6,0/4],[0/5,0/6,2/6],[0/5,0/5,0/6]].
% In 'top', this went up to 11% of my 64GB RAM!
% Also, sadly, I see total time nearly doubled compared with d_gs_rec/3!


% Now what about creating the strata?  Do I already have the
% needed predicate?  Not quite, I think: sift/3 builds strata
% for an entire set without regard to the dose recommendation.
% Here, all I want is the maximal elements (i.e., *top* strata)
% for each dose-recommendation level within 𝒬f.
% Note that 𝒬f is in practice so small that qs_maxs/2 should
% do just fine to start.  (TODO: But I really should test this
% claim once gₓ calculations for higher D's become feasible!)

d_Qfstratamax(D, Mss) :-
    must_be(integer, D),
    findall(X-Q, d_endtally_rec(D,Q,X), XQs),
    sort(XQs, SXQs),
    group_pairs_by_key(SXQs, GXQs),
    pairs_values(GXQs, Qss),
    maplist(qs_maxs, Qss, Mss).

% These queries corroborate the d_Qfstratamax/2 results below.
%?- D=3, X=3, Maxs+\(findall(Qf, d_endtally_rec(D, Qf, X), Qfs), qs_maxs(Qfs, Maxs)).

%?- d_Qfstratamax(2, Mss), maplist(portray_clause, Mss).
%@ [[2/6,0/0],[2/6,2/6]].
%@ [[0/6,2/6]].
%@ [[0/3,0/6],[1/6,0/6]].
%@    Mss = [[[2/6,0/0],[2/6,2/6]],[[0/6,2/6]],[[0/3,0/6],[1/6,0/6]]].

%?- d_Qfstratamax(3, Mss), maplist(portray_clause, Mss).
%@ [[2/6,0/0,0/0],[2/6,2/6,0/0],[2/6,2/6,2/6]].
%@ [[0/6,2/6,0/0],[0/6,2/6,2/6]].
%@ [[0/3,0/6,2/6],[1/6,0/6,2/6]].
%@ [[0/3,0/3,0/6],[0/3,1/6,0/6],[1/6,0/3,0/6],[1/6,1/6,0/6]].
%@    Mss = [[[2/6,0/0,0/0],[2/6,2/6,0/0],[2/6,2/6,2/6]],[[0/6,2/6,0/0],[0/6,2/6,2/6]],[[0/3,0/6,2/6],[1/6,0/6,2/6]],[[0/3,0/3,0/6],[0/3,1/6,0/6],[1/6,0/3,0/6],[1/6,1/6,0/6]]].

%?- d_Qfstratamax(4, Mss), maplist(portray_clause, Mss).
%@ [[2/6,0/0,0/0,0/0],[2/6,2/6,0/0,0/0],[2/6,2/6,2/6,0/0],[2/6,2/6,2/6,2/6]].
%@ [[0/6,2/6,0/0,0/0],[0/6,2/6,2/6,0/0],[0/6,2/6,2/6,2/6]].
%@ [[0/3,0/6,2/6,0/0],[0/3,0/6,2/6,2/6],[1/6,0/6,2/6,0/0],[1/6,0/6,2/6,2/6]].
%@ [[0/3,0/3,0/6,2/6],[0/3,1/6,0/6,2/6],[1/6,0/3,0/6,2/6],[1/6,1/6,0/6,2/6]].
%@ [[0/3,0/3,0/3,0/6],[0/3,0/3,1/6,0/6],[0/3,1/6,0/3,0/6],[0/3,1/6,1/6,0/6],[1/6,0/3,0/3,0/6],[1/6,0/3,1/6,0/6],[1/6,1/6,0/3,0/6],[1/6,1/6,1/6,0/6]].
%@    Mss = [[[2/6,0/0,0/0,0/0],[2/6,2/6,0/0,0/0],[2/6,2/6,2/6,0/0],[2/6,2/6,2/6,2/6]],[[0/6,2/6,0/0,0/0],[0/6,2/6,2/6,0/0],[0/6,2/6,2/6,2/6]],[[0/3,0/6,2/6,0/0],[0/3,0/6,2/6,2/6],[1/6,0/6,2/6,0/0],[1/6,0/6,2/6,2/6]],[[0/3,0/3,0/6,2/6],[0/3,1/6,0/6,2/6],[1/6,0/3,0/6,2/6],[1/6,1/6,0/6,2/6]],[[0/3,0/3,0/3,0/6],[0/3,0/3,1/6,0/6],[0/3,1/6,0/3,0/6],[0/3,1/6,1/6,0/6],[1/6,0/3,0/3,0/6],[1/6,0/3,1/6,0/6],[1/6,1/6,0/3,0/6],[1/6,1/6,1/6,0/6]]].

% ============================================================
% Investigate non-functorialities in the D=3 trial:

/*
?- d_endtally_rec(3, Q1, D1),
   d_endtally_rec(3, Q2, D2),
   Q1 '≼' Q2, % Q1 evidently no safer than Q2,
   D1 #>  D2. % yet recommended D1 exceeds D2.
%@    Q1 = [0/3,1/6,1/6], D1 = 3, Q2 = [0/3,0/6,2/6], D2 = 2
%@ ;  Q1 = [1/6,1/6,1/6], D1 = 3, Q2 = [1/6,0/6,2/6], D2 = 2
%@ ;  Q1 = [1/6,1/6,2/3], D1 = 2, Q2 = [0/6,2/6,2/3], D2 = 1
%@ ;  Q1 = [1/6,1/6,2/3], D1 = 2, Q2 = [0/6,2/6,2/6], D2 = 1
%@ ;  Q1 = [1/6,1/6,2/6], D1 = 2, Q2 = [0/6,2/6,2/6], D2 = 1
%@ ;  Q1 = [1/6,1/6,3/3], D1 = 2, Q2 = [0/6,2/6,0/0], D2 = 1
%@ ;  Q1 = [1/6,1/6,3/3], D1 = 2, Q2 = [0/6,2/6,2/3], D2 = 1
%@ ;  Q1 = [1/6,1/6,3/3], D1 = 2, Q2 = [0/6,2/6,2/6], D2 = 1
%@ ;  Q1 = [1/6,1/6,3/3], D1 = 2, Q2 = [0/6,2/6,3/3], D2 = 1
%@ ;  Q1 = [1/6,1/6,3/3], D1 = 2, Q2 = [0/6,2/6,3/6], D2 = 1
%@ ;  Q1 = [1/6,1/6,3/6], D1 = 2, Q2 = [0/6,2/6,2/6], D2 = 1
%@ ;  Q1 = [1/6,1/6,3/6], D1 = 2, Q2 = [0/6,2/6,3/6], D2 = 1
%@ ;  Q1 = [1/6,1/6,4/6], D1 = 2, Q2 = [0/6,2/6,2/6], D2 = 1
%@ ;  Q1 = [1/6,1/6,4/6], D1 = 2, Q2 = [0/6,2/6,3/6], D2 = 1
%@ ;  Q1 = [1/6,1/6,4/6], D1 = 2, Q2 = [0/6,2/6,4/6], D2 = 1
%@ ;  false. % 15 non-functorial pairs in D=3 trial!
*/

% Are any of these pharmacologic non-monotonicities genuinely new?
% How many reduce to the lone D=2 case of [1/6,1/6] vs [0/6,2/6],
% after projecting off one dose?
% All of them, in fact!  The first two solutions reduce thus upon
% projecting off the lowest dose, and the remaining 13 do so when
% the top dose is removed.

%:- table d_mendtally_rec_/4. % TODO: Understand why I cannot table this.
% (I can hardly use tabling safely, if I don't understand why it failed here!)
d_mendtally_rec(D, Q, X) :- d_mendtally_rec_(D, Q, X, _).

d_mendtally_rec_(D, Q, X, Xls) :-
    d_endtally_rec(D, Q, Xu), % Q-Xu is a final tally w/ *unrectified* rec, from a D-dose 3+3
    findall(Xl, (d_endtally_rec(D, Ql, Xl),
                 Xu #> Xl,  % Final tally Ql received a rec *lower* than Xu,
                 Q '≼' Ql), % although it is evidently at least as safe as Q.
            Xls),
    foldl(clpz:min_, Xls, Xu, X).

%?- d_mendtally_rec_(3, Q, D, [_|_]).
%@    Q = [0/3,1/6,1/6], D = 2
%@ ;  Q = [1/6,1/6,1/6], D = 2
%@ ;  Q = [1/6,1/6,2/3], D = 1
%@ ;  Q = [1/6,1/6,2/6], D = 1
%@ ;  Q = [1/6,1/6,3/3], D = 1
%@ ;  Q = [1/6,1/6,3/6], D = 1
%@ ;  Q = [1/6,1/6,4/6], D = 1
%@ ;  false.
% NB: Indeed there were only 7 unique Q1's
%     among the 15 solutions found above.

/*
TODO:

1. I must take stock of the foregoing efforts in light of the clearer view
afforded by the monograph's Kan-extension motivation for Galois enrollments.
Where the foregoing now seem in retrospect ill-considered or doomed to fail,
let me expunge them with suitably commented git commits.

- One major distraction above relates to my now-abandoned speculation about
  needing to extend ≼.

- Another distracting technicality is the special code for early exploration
  of the D=2 case.

- All discussion around approximating from above/below via aₓ & bₓ can go,
  now that I have a well-developed theory grounded in the Kan extension
  and properly defined gₓ & ℓₓ.

2. Revisit the feasibility of Hasse diagrams.

- Try implementing the https://en.wikipedia.org/wiki/Covering_relation.

- Shouldn't a Hasse diagram for 𝒬f be possible, at least in D=2 case,
  and maybe even for D=3 as well?

3. Simulate and visualize rolling-enrollment trials.

4. In Prolog code, explore the possibility of implementing join & meet
   operations.  Are these well-defined?  Does that make 𝒬 a _lattice_,
   or even a _complete lattice_?

   - It is interesting to note how abandoning the idea of enlarging ≼
     has directly enabled these considerations.  There may well be a
     role for calling 𝒬 a lattice!

*/
