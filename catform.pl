% Inline code for Categorical sketch

:- use_module(library(lists)).
:- use_module(library(clpz)).
:- use_module(library(reif)).
:- use_module(library(dcgs)).
:- use_module(library(error)).
:- use_module(library(si)).
:- use_module(library(lambda)).
:- use_module(library(pairs)).
:- use_module(library(time)).
:- use_module(library(format)).
:- use_module(library(debug)).
:- use_module(library(tabling)).

:- use_module(rcpearl).
:- use_module(rectify).

:- table endtally_rec/2.

% This predicate describes precisely the final tallies and dose recommendations
% which terminate the paths of the 2-dose 3+3 design as described by our DCG.
% Memoizing it via *tabling* supports a _complete_ description at the cost of
% only a single comprehensive elaboration of the DCG.
endtally_rec(FinalTally, Rec) :-
    phrase(path([0/0]-[0/0]), Path),
    phrase((..., [Endstate,stop,recommend_dose(Rec)]), Path),
    state_tallies(Endstate, FinalTally).
    
%?- endtally_rec(Q, D).
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
?- endtally_rec(Q1, D1),
   endtally_rec(Q2, D2),
   Q1 =<$ Q2, % Q1 evidently no safer than Q2,
   D1 #>  D2. % yet recommended D1 exceeds D2.
%@    Q1 = [1/6,1/6], D1 = 2, Q2 = [0/6,2/6], D2 = 1
%@ ;  false.
*/

% A different way to put this would be:
/*
?- endtally_rec(Q1, D1),
   endtally_rec(Q2, D2),
      Q1 =<$ Q2,  % Q1 is evidently no safer than Q2,
   #\(D1 #=< D2). % yet D1 is NOT likewise related to D2.
%@    Q1 = [1/6,1/6], D1 = 2, Q2 = [0/6,2/6], D2 = 1
%@ ;  false.
*/

% That initial listing in Section 4.1 ought to have been done with
% this predicate too!
/*
?- N+\(setof(Q-Rec, endtally_rec(Q, Rec), QRecs),
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

% Let's now expand the information extracted from the 3+3 design
% to include all next-dose recommendations:

:- table tally_nextdose/2.

tally_nextdose(Tally, D) :-
    Init = [0/0]-[0/0],
    phrase(path(Init), Path),
    phrase((..., [Ls-Hs,E], ...), [Init|Path]),
    length(Ls, D0),
    (   E = esc, #D #= D0 + 1
    ;   E = sta, #D #= D0
    ;   E = des, #D #= D0 - 1
    ),
    state_tallies(Ls-Hs, Tally).

/*
%?- tally_nextdose(Tally, D).
%@    Tally = [0/0,0/0], D = 1
%@ ;  Tally = [0/3,0/0], D = 2
%@ ;  Tally = [0/3,0/3], D = 2
%@ ;  Tally = [0/3,1/3], D = 2
%@ ;  Tally = [0/3,2/3], D = 1
%@ ;  Tally = [0/3,2/6], D = 1
%@ ;  Tally = [0/3,3/3], D = 1
%@ ;  Tally = [0/3,3/6], D = 1
%@ ;  Tally = [0/3,4/6], D = 1
%@ ;  Tally = [1/3,0/0], D = 1
%@ ;  Tally = [1/6,0/0], D = 2
%@ ;  Tally = [1/6,0/3], D = 2
%@ ;  Tally = [1/6,1/3], D = 2
%@ ;  false. % Why only N=13 answers?
*/

/*
My hand-tabulated next-dose pairs in 'rectify.pl' were:

/next3plus3([0/0,0/0], 1).
/next3plus3([0/3,0/0], 2). % 1st cohort from ~,~
/next3plus3([1/3,0/0], 1).
-next3plus3([2/3,0/0], 0).
-next3plus3([3/3,0/0], 0).
/next3plus3([0/3,0/3], 2). % 2nd cohorts from 0,~
/next3plus3([0/3,1/3], 2).
/next3plus3([0/3,2/3], 1).
/next3plus3([0/3,3/3], 1).
/next3plus3([1/6,0/0], 2). % 2nd cohorts from 1,~
-next3plus3([2/6,0/0], 0).
-next3plus3([3/6,0/0], 0).
-next3plus3([4/6,0/0], 0).
/next3plus3([1/6,0/3], 2). % 3rd cohorts from 1',~
/next3plus3([1/6,1/3], 2).
-next3plus3([1/6,2/3], 1).
-next3plus3([1/6,3/3], 1).

This goes to show that I do need Prolog's help here,
even in the simplest case.
*/

/*
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
*/

/*
?- setof(FinalTally - Rec,
         FinalTally^Rec+\(phrase(path([0/0]-[0/0]), Path),
                          reverse(Path, [recommend_dose(Rec),stop,Endstate|_]),
                          state_tallies(Endstate, FinalTally)),
         TallyRecs),
   maplist(portray_clause, TallyRecs),
   length(TallyRecs, N),
   Nu+\(list_to_set(TallyRecs, Unique), length(Unique, Nu)).
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
%@    TallyRecs = [[0/3,0/6]-2,[0/3,1/6]-2,[0/6,2/3]-1,[0/6,2/6]-1,[0/6,3/3]-1,[0/6,3/6]-1,[0/6,4/6]-1,[1/6,0/6]-2,[1/6,1/6]-2,[1/6,2/3]-1,[1/6,2/6]-1,[1/6,3/3]-1,[1/6,3/6]-1,[1/6,4/6]-1,[2/3,0/0]-0,[2/6,0/0]-0,[2/6,2/3]-0,[2/6,... / ...]-0,[... / ...|...]-0,... - ...|...], N = 29, Nu = 29.
*/

/*
?- X^Dx^Y^Dy+\(setof(FinalTally - Rec,
                     FinalTally^Rec+\(phrase(path([0/0]-[0/0]), Path),
                                      reverse(Path, [recommend_dose(Rec),
                                                     stop,Endstate|_]),
                                      state_tallies(Endstate, FinalTally)),
                     TallyRecs),
               member(X-Dx, TallyRecs),
               member(Y-Dy, TallyRecs),
               #Dx #> #Dy,
               X =<$ Y).
%@    X = [1/6,1/6], Dx = 2, Y = [0/6,2/6], Dy = 1
%@ ;  false.
*/
