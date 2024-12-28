% enst.pl
% Evidently-no-safer-than relation and friends

:- module(enst, [
              % Pending https://github.com/mthom/scryer-prolog/issues/2547,
              % we cannot export some pretty operators.  Client modules may
              % however access these by explicit qualification, and assign
              % these operators locally.
              %% op(900, xfx, '≼'),
              %% op(900, xfx, '⋠'),
              %% op(900, xfx, '≽'),
              %% op(900, xfx, '≺'),
              %% op(900, xfx, '⊁'),
              join/3,
              meet/3,
              %coefs/3, % TODO: Consider absorbing qs_int/2, which uses this.
              qs_int/2,
              po_qs_sorted/3,
              minimal_in/2,
              in_cover/3,
              d_writehassedot/1
	  ]).

:- use_module(library(lists)).
:- use_module(library(clpz)).
:- use_module(library(reif)).
:- use_module(library(lambda)).
:- use_module(library(iso_ext)).
:- use_module(intlist).
:- use_module(tally).
:- use_module(freebase).
:- use_module(library(pairs)).
:- use_module(run33).
:- use_module(library(format)).
:- use_module(library(assoc)).
:- use_module(library(time)).

clpz:monotonic. % The error occurs with or without this declaration.

:- op(900, xfx, '≼').
:- op(900, xfx, '⋠'). % d_starts1/1 uses '⋠'/2
:- op(900, xfx, '≽').

:- op(900, xfx, '≺'). % in_cover_t/4 uses '≺'/2 and between_t/4 uses '≺'/3
:- op(900, xfx, '⊁'). % minimal_in/2 uses '⊁'/2


% Impose global default for R here:
coefs(Qs, Ys, Hs) :- coefs(2, Qs, Ys, Hs).
etas_enc(Hs, HK) :- r_etas_enc(2, Hs, HK).

%?- [1/6,1/3] '≼' [1/6,0/0].
%@    false. % with R=1
%?- [1/6,1/3] '≼' [1/6,0/0].
%@    true. % with R=2

% Find the unique coefficients of ≼ᵣ-generators for given q ∈ Qᴰ.
coefs(R, Qs, Ys, Hs) :-
    #R #> 0,
    same_length(Qs, Ys), % allows usage (+R, -Qs, +Ys, +Hs)
    maplist(\Q^T^N^(Q = T/N), Qs, Ts, Ns),
    % We will set Ys = [γs] (of length D), with γᴅ being coef of ≼₁﹕ᵣ.
    % Our first D equations are simply that Ys is minus partial sums of Ts.
    intlist_negated(Ts, NegTs), intlist_partsums(NegTs, Ys),
    reverse(Ys, [YD|_]),
    % Our next set of equations is η₀ = ΣU - rΣTρ = ΣU + r·γᴅ,
    % and then recursively ηₖ = ηₖ₋₁ - nₖ for k in 1..D-1.
    % But an even simpler expression of this, which dispenses
    % altogether with the Us, is to reverse-partial-sum the Ns,
    % then add Yᴅ*(R+1)!
    reverse(Ns, Иs),
    intlist_partsums(Иs, ΣИs),
    reverse(ΣИs, ΞNs),
    #RhoR1 #= #YD * (#R + 1),
    maplist(sum_(RhoR1), ΞNs, Hs).

sum_(Z1, Z2, Sum) :- #Sum #= #Z1 + #Z2.
diff_(Z1, Z2, Diff) :- #Diff #= #Z1 - #Z2.

%?- coefs(1, [0/0,0/0,0/0], Ys, Hs).
%@    Ys = [0,0,0], Hs = [0,0,0].

%?- transform([0/0,0/0,0/0], [1/2,3/4,4/5], Ys, Hs).
%@    Ys = [-1,-4,-8], Hs = [-13,-15,-19]. % R=2
%@    Ys = [-1,-4,-8], Hs = [-5,-7,-11].   % R=1
%?- coefs(1, [1/2,3/4,4/5], Ys, Hs).
%@    Ys = [-1,-4,-8], Hs = [-5,-7,-11].

% I've now worked out in detail a unique transformation of pair
% Q1,Q2 ∈ Qᴰ into 2✕D parameters, *all* nonnegative iff Q1 ⊑ Q2.
transform(Q1s, Q2s, ΔHs, ΔOs) :-
    same_length(Q1s, Q2s),
    coefs(Q1s, H1s, O1s),
    coefs(Q2s, H2s, O2s),
    maplist(diff_, H2s, H1s, ΔHs),
    maplist(diff_, O2s, O1s, ΔOs).

%?- transform([1/1,0/1], [0/1,1/1], Hs, Os).
%@    Hs = [1,0], Os = [0,0].
%?- transform([0/1,1/1], [0/0,1/2], Hs, Os).
%@    Hs = [0,0], Os = [0,1].
%?- transform([0/1,1/2], [0/1,0/0], Hs, Os).
%@    Hs = [0,1], Os = [0,0].

%?- transform([0/2,1/2], Q2, [0,1], [1,0]).
%@    Q2 = [0/3,0/0].
%?- transform([0/2,1/2], Q2, [0,1], [1,1]).
%@    Q2 = [0/2,0/1].

#>(X, Y, Truth) :- clpz_t(X #> Y, Truth). % counterpart to clpz:(#<)/3

'≼'(Q1s, Q2s, Truth) :- % QAs ≼toxD QBs ≼tol1 QCs ≼exch QZs
    transform(Q1s, Q2s, Hs, Os),
    % It's as simple now as asserting all Hs & Os are nonnegative!
    % But the more effective way to express this may be to look
    % for any single negative value, then invert truth value.
    if_((   tmember_t(#>(0), Hs)
        ;   tmember_t(#>(0), Os)
        ), Truth = false,
        Truth = true
       ).


'≺'(Q1s, Q2s, Truth) :-
    if_((Q1s '≼' Q2s, dif(Q1s, Q2s)),
        Truth = true,
        Truth = false
        ).

'⋠'(Q1s, Q2s, Truth) :- '≼'(Q1s, Q2s, Falsity),
                        reif:non(Falsity, Truth).

'≽'(Q2s, Q1s, Truth) :-'≼'(Q1s, Q2s, Truth).

'≼'(Q1s, Q2s) :- '≼'(Q1s, Q2s, true).
'⋠'(Q1s, Q2s) :- '≼'(Q1s, Q2s, false).
'≽'(Q2s, Q1s) :- '≼'(Q1s, Q2s, true).

'≺'(Q1s, Q2s) :- '≺'(Q1s, Q2s, true).
'⊁'(Q2s, Q1s) :- '≺'(Q1s, Q2s, false).

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

meet_(Q1s, Q2s, Ys, Hs) :-
    same_length(Q1s, Q2s),
    coefs(Q1s, Y1s, H1s),
    coefs(Q2s, Y2s, H2s),
    mins(Y1s, Y2s, Ys),
    mins(H1s, H2s, Hs).

meet_(Q1s, Q2s, Qs) :- % 'formal meet'
    meet_(Q1s, Q2s, Ys, Hs),
    coefs(Qs, Ys, Hs).

%?- meet_([3/3,4/4], [4/6,0/0], M).
%@    M = [4/3,3/4]. % Not a valid tally!

% Let's try to find some very small examples!
meet_invalid(Q1, Q2, M) :-
    Nmax in 0..3, indomain(Nmax),
    N1 in 0..Nmax, indomain(N1),
    N2 in 0..Nmax, indomain(N2),
    qs_d_nmax(Q1, 2, N1),
    qs_d_nmax(Q2, 2, N2),
    meet_(Q1, Q2, M),
    member(T/N, M),
    #T #> #N.

%?- meet_invalid(Q1, Q2, M).
%@    Q1 = [0/0,1/1], Q2 = [1/1,0/1], M = [1/0,0/1]
%@ ;  Q1 = [1/1,0/1], Q2 = [0/0,1/1], M = [1/0,0/1]
%@ ;  Q1 = [0/0,1/1], Q2 = [1/1,0/1], M = [1/0,0/1]
%@ ;  Q1 = [1/1,0/1], Q2 = [0/0,1/1], M = [1/0,0/1]
%@ ;  Q1 = [0/0,1/1], Q2 = [1/1,0/1], M = [1/0,0/1]
%@ ;  Q1 = [0/0,1/1], Q2 = [1/1,0/2], M = [1/0,0/1]
%@ ;  ... . % Well, that's more like it!

% So we now have some very simple examples of tally pairs
% that do not have a valid meet.

% Unlike meet_/3, which allows for 'imaginary' meets,
% this predicate succeeds only if a valid meet obtains.
meet(Q1s, Q2s, Qs) :-
    meet_(Q1s, Q2s, Qs),
    maplist(\Q^(Q=T/N, #T #=< #N), Qs).

join(Q1s, Q2s, Ys, Hs) :-
    same_length(Q1s, Q2s),
    coefs(Q1s, Y1s, H1s),
    coefs(Q2s, Y2s, H2s),
    maxs(Y1s, Y2s, Ys),
    maxs(H1s, H2s, Hs).

% NB: If, as I believe, 𝒬 = (Qᴰ,≼) is an upper semilattice,
%     then these joins will always exist and are unique.
join(Q1s, Q2s, Qs) :-
    join(Q1s, Q2s, Ys, Hs),
    coefs(Qs, Ys, Hs).

% ---------- Embedding stuff ----------


qs_int(Qs, K) :-
    coefs(Qs, Ys, Hs),
    gammas_enc(Ys, YK),
    etas_enc(Hs, HK),
    same_length(Ys, _s), placevalues([P|_s]),
    #K #= #HK * #P + #YK.

%?- qs_int([1/1,2/3], K).
%@    K = -17403.

%?- Qs = [0/0,0/0], qs_int(Qs, K).
%@    Qs = [0/0,0/0], K = 0.

% ---------- Sorting ----------

po_qs_sorted('≼', Qs, AscQs) :-
    maplist(qs_int, Qs, Ks),
    pairs_keys_values(KQs, Ks, Qs),
    sort(KQs, SKQs),
    pairs_values(SKQs, AscQs).

po_qs_sorted('≽', Qs, DescQs) :-
    po_qs_sorted('≼', Qs, AscQs),
    reverse(AscQs, DescQs).

% ---------- Minimal & Maximal sets ----------

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
    phrase(format_("HasseD~d.dot", [D]), Filename),
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

