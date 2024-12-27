% freebase.pl
% Integer encoding of variable-base integers.
% Module name is meant to suggest inadvisability.
% Observe that much of the code here is highly
% specific to the Nmax=6 premise of 3+3 design.

:- module(freebase, [
              gammas_enc/2,
              r_etas_enc/3,
              placevalues/1
	  ]).

:- use_module(library(lists)).
:- use_module(library(clpz)).
:- use_module(library(reif)).

clpz:monotonic.

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

% To encode the γs, we can reuse existing infrastructure, as-is
gammas_enc(Ys, K) :- ws_int(Ys, K).

% To encode ηs, we need only encode a base-(6*D*(R+1)+1) integer.
% (Note that we need not even insist on non-negative 'digits',
% since any bias in a given digit will bias the whole encoding
% consistently, with no effect on the _order_.)
r_etas_enc(R, Hs, K) :-
    r_etas_base(R, Hs, B),
    foldl(base_(B), Hs, 0, K).

r_etas_base(R, Hs, B) :-
    #R #> 0, length(Hs, D),
    #B #= 6 * #D * (#R+1) + 1.

base_(B, A, N0, N) :- #N #= #B * #N0 + #A.

%?- foldl(base_(10), [1,2,3,4], 0, N).
%@    N = 1234.

%?- Hs = [18,12,6], r_etas_enc(1, Hs, K).
%@    Hs = [18,12,6], K = 25092.

