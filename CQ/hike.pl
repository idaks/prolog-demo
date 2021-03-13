% The query Q: 
hike(X,Z1,Z2,Y) :- e(X,Z1), e(Z1,Z2), e(Z2,Y).

% The underlying domain (one constant per variable):
dom(X) :- member(X, [a,b,c,d]).

% The Herbrand Base B_D^Q for the canonical database D^Q: 
e(X,Y) :- dom(X), dom(Y).

% All homomorphisms (= all ways to answer Q over the Herbrand Base):
homs(Hs) :- setof(h(X,Z1,Z2,Y), hike(X,Z1,Z2,Y), Hs).

go :-
    homs(Hs),
    length(Hs,N),
    format('% ~w homomorphisms found:~n', N),
    member(H,Hs),
    format('~w.~n', H), 
    fail
    ;
    true.

:- go.

