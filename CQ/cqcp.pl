% ---------------------------------------------------------
% Conjunctive Query Containment and Minimization Algorithms
% File:		 cqcp.swi
% Last modified: 08/06/2003
% Author:        Bertram Ludaescher (ludaesch@sdsc.edu)
% ---------------------------------------------------------- 

:- op(600,xfx,::).  % for naming queries: Qid :: Query
:- op(500,xfx,<-).  % Query syntax: QueryHead <- [QueryBody].


% query_file(F)
% F contains queries to be processed. Query format is:
%        QueryId ::  QueryHead  <- [ QueryBody ].
% Format for integrity constraints (in denial form) is:
%       ic(DenialId) ::  false(...) <- [ Denial ].
query_file('sample.swi').
query_file('uncle_queries.swi').
query_file('ecs265.swi').


% Test everything
go :-
	query_file(F),
	load_queries(F),
	test_contained_all,
	test_irrelevant_all,
	test_minimal_all,
	fail
	;
	true.

% Some simple profiling. It seems that profile/1 works
% only on "second try", hence the go(1) first ...
go_profile(N) :-
	go(1),          
	profile(go(N)). 

% Go N times
go(N) :-
	tell('dummy'),
	between(1,N,_),
	go,
	fail
	;
	told.


% Load queries from first query_file
load_queries :-
	query_file(F),
	load_queries(F).

% Load queries from file F, discarding earlier queries,
% thus files are processed independently
load_queries(F) :-
	format('~n~`=t LOADING ~w ~`=t~78|~n', [F]),
	retractall( _Qid :: _Query1 ),    % discard any earlier queries 
	see(F),
	repeat,
	read(Term),
	(Term = end_of_file
	 ->	true
	 ;	assert( Term ), % Term = QueryId :: QueryHead <- [ QueryBody ]
		fail
	),!,
	seen,
	listing( :: ),			 % show what has been loaded
	findall(Id, Id :: _Query2 , Ids), % get a list of all query ids 
	length(Ids, Count),		 % and count them
	format('% total of ~w queries loaded.~n',[Count]).

% Test all queries against each other for containment (= O(n^2) tests for n queries)
test_contained_all :- 
	format('~n~`-t CONTAINMENT TESTS~`-t~78|~n'),
	Qid1 :: Q1,
	Qid2 :: Q2,
	Qid1 \= Qid2,      % to avoid testing with oneself
	copy_term(Q1,Q1P),
	numbervars(Q1P, 1,_, [functor_name('$x')]),
	copy_term(Q2,Q2P),
	numbervars(Q2P, 1,_, [functor_name('$y')]),
	(contained(Q1, Q2, Sigma)
	 ->	format('~n~w => ~w; sigma = ~p~n',[Qid1, Qid2,Sigma]), % containment holds
		format('  ~p =>~n  ~p~n', [Q1P,Q2P]) 
	 ;	format('.')		% print '.' otherwise
	),
	fail
	;      
	true.

% Test which queries are irrelevant due to integrity contraints
test_irrelevant_all :-
	format('~n~`-t INTEGRITY CONSTRAINTS TESTS ~`-t~78|~n'),
	Qid :: Q_Head <- Q_Body,		% pick a query  
	Qid \= ic(_),				% ... but not a constraint
	ic(ICid) :: IC_Head <- IC_Body,		% pick a constraint
	(contained(q <- Q_Body , q <- IC_Body, _)
	 ->	format('~n~w is UNSATISFIABLE for ic(~w)~n',[Qid, ICid]), 
		format('  ~p =>~n  ~p~n', [Q_Head <- Q_Body, IC_Head <-IC_Body]) 
	 ;	format('.')		% print '.' otherwise
	),
	fail
	;
	true.

% Minimize all queries
test_minimal_all :- 	
	format('~n~`-t MINIMIZATIONS ~`-t~78|~n'),
	Qid :: Vs<-Q,
	minimal(Vs<-Q, M),
%	numbervars(Vs<-Q, '$VAR', 0,_),
	numbervars(Vs<-Q, 0, _, [functor_name('$VAR')]),
	length(Q,Q_len), length(M,M_len),
	(Q_len = M_len
	 ->	format('~w is minimal:~n    ~p~n',
		       [Qid, Vs<-Q])
	 ;	format('~w CAN BE MINIMIZED:~n    ~p~n<=> ~p~n',
		       [Qid, Vs<-Q, Vs<-M])
	),
	fail
	;
	true.

%============= CQCP Conjunctive Query Containment in Prolog ==============

% Q1 contained in Q2  <=>  Q2 has an answer over the canonical_db(Q1)
contained(V1s<-Q1,  V2s<-Q2, Sigma) :-	   % unify head variables Vs
%	numbervars(V1s<-Q1, '$a', 1,_),    % freeze Q1 => canonical_db D
	numbervars(V1s<-Q1, 1, _, [functor_name('$a')]),    % freeze Q1 => canonical_db D
	free_variables(V2s<-Q2, Sigma),
        V1s = V2s,
	satisfied(Q2,Q1).	% evaluate Q2 over D

% satisfied(+As, +DB)
% is true if ALL atoms As can be made true in database DB
satisfied([], _).		  % empty conjunction => true
satisfied([A|As], DB) :-
	member(A, DB),		  % if atom A can be satisfied in DB => OK; else fail
	satisfied(As, DB).	  % continue with rest

%============= CQMP Conjunctive Query Minimization in Prolog ==============

% minimal(+Query, -MinimizedQuery)
minimal(Vs<-Body, MinBody) :-
	minimal(Vs<-Body, [], MinBody).

%%% minimal(+Query, +MinimalSoFar,-MinimizedQuery)
% compute minimal version of Q, MinimalSoFar accumulates
minimal(_<-[], Ms, Ms).
minimal(Vs<-[B|Bs], Ms, MinBody) :-	            % pick an atom B
	append(Ms,Bs,MsBs),		            % everything but B
	copy_term(Vs<-MsBs, Vs_MsBs_new),           % make fresh copy of Q1
 	(\+ \+ contained(Vs_MsBs_new, Vs<-[B|MsBs],_) % \+\+ to undo bindings
	 ->	minimal(Vs<-Bs,Ms,MinBody)	    % B can be dropped
	 ;	minimal(Vs<-Bs,[B|Ms],MinBody)	    % B is in the minimal query
	).
%==========================================================================

% For pretty printing '$a'(i) without '$' and parentheses
portray('$a'(X)) :-
	format('c~w',[X]).

portray('$x'(X)) :-
	format('X~w',[X]).

portray('$y'(X)) :-
	format('Y~w',[X]).



	
