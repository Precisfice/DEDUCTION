% hasse.pl
% Hasse diagrams for D in 2..3 cases

:- use_module(library(lists)).
:- use_module(library(clpz)).
:- use_module(library(reif)).
:- use_module(library(lambda)).
:- use_module(library(iso_ext)).
:- use_module('../intlist.pl').
:- use_module('../tally.pl').
:- use_module('../enst.pl').
:- use_module(library(pairs)).
:- use_module('../run33.pl').
:- use_module(library(format)).
:- use_module(library(assoc)).
:- use_module(library(time)).

clpz:monotonic.

% Pending https://github.com/mthom/scryer-prolog/issues/2547,
% some pretty operators resist export, and require 'extraction':
:- op(900, xfx, '≼').
:- op(900, xfx, '≺').
:- op(900, xfx, '⊁').

'≼'(X,Y,T) :- enst:'≼'(X,Y,T).
'≼'(X,Y) :- enst:'≼'(X,Y).

'≺'(Q1s, Q2s, T) :- enst:'≺'(Q1s, Q2s, T). % used by between_t/4 
'≺'(Q1s, Q2s) :- '≺'(Q1s, Q2s, true).      % used by in_cover_t/4
'⊁'(Q2s, Q1s) :- '≺'(Q1s, Q2s, false).     % used by minimal_in/2

% ---------- the Covering relation ----------

% Suppose we take a list (qua set) of all final tallies, and
% recursively peel off the minimal elements, i.e. those which
% have no arrows into the remainder.
minimal_in(M, Qs) :-
    member(M, Qs),
    maplist('⊁'(M), Qs).

/*
?- Ms+\(findall(Q, d_endtally_rec(2,Q,_), FinalTallies),
        findall(M, minimal_in(M, FinalTallies), Ms)).
%@    Ms = [[3/6,4/6],[4/6,0/0]].
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

% ---------- Hasse diagram ----------

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

% Write out Hasse diagram as (GraphViz) DOT file.
d_writehassedot(D) :-
    phrase(format_("../HasseD~d.dot", [D]), Filename),
    atom_chars(File, Filename),
    format("Opening file ~q...~n", [File]), % feedback to console
    setup_call_cleanup(open(File, write, OS),
		       (   format("Collecting final tallies ..", []),
                           % We use _unrectified_ d_endtally_rec/3 to exhibit
                           % the non-functoriality of default 3+3 dose recs.
                           setof(Q-X, d_endtally_rec(D,Q,X), QXs),
                           pairs_keys(QXs, Qs),
                           length(Qs, Nf),
                           format("~n sorting ~d final tallies ..", [Nf]),
                           po_qs_sorted('≽', Qs, DescQs),
                           format("~n stratifying ..~n", []),
                           foldl(sift, DescQs, [[]], Qss),
                           reverse(Qss, RQss), maplist(portray_clause, RQss),
                           format(OS, "strict digraph hasseD~d {~n", [D]),
                           format(OS, "  rankdir=~a;~n", ['BT']),
                           format(OS, "  node [colorscheme=~w, fontname=\"~w\"];~n",
                                  ['set14','Helvetica:bold']),
                           format("Writing strata to DOT file ..", []),
                           list_to_assoc(QXs, QXassoc),
                           maplist(write_stratum(OS,QXassoc), Qss),
                           format("~n writing covering relation ..", []) ->
                           reverse(DescQs, AscQs), % speeds cover calculation
                           time((   in_cover(AscQs, Q1, Q2),
			            format(OS, "  \"~w\" -> \"~w\";~n",
                                           [Q1,Q2]),
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
%@ Opening file '../HasseD2.dot'...
%@ Collecting final tallies ..
%@  sorting 29 final tallies ..
%@  stratifying ..
%@ [[0/3,0/6]].
%@ [[0/3,1/6],[1/6,0/6]].
%@ [[0/6,2/6]].
%@ [[0/6,2/3],[1/6,1/6]].
%@ [[2/6,0/0],[0/6,3/6]].
%@ [[2/3,0/0],[0/6,3/3],[1/6,2/6]].
%@ [[0/6,4/6],[1/6,2/3]].
%@ [[3/6,0/0],[1/6,3/6]].
%@ [[3/3,0/0],[1/6,3/3],[2/6,2/6]].
%@ [[1/6,4/6],[2/6,2/3]].
%@ [[4/6,0/0],[2/6,3/6]].
%@ [[2/6,3/3],[3/6,2/6]].
%@ [[2/6,4/6],[3/6,2/3]].
%@ [[3/6,3/6]].
%@ [[3/6,3/3]].
%@ [[3/6,4/6]].
%@ Writing strata to DOT file ..
%@  writing covering relation ..   % CPU time: 6.586s, 34_163_953 inferences
%@ .. done.
%@    true.

