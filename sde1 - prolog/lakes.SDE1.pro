%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% ECE3520/CpSc3520 SDE1: Prolog Declarative and Logic Programming

% Use the following Prolog relations as a database of familial 
% relationships for 4 generations of people.  If you find obvious
% minor errors (typos) you may correct them.  You may add additional
% data if you like but you do not have to.

% Then write Prolog rules to encode the relations listed at the bottom.
% You may create additional predicates as needed to accomplish this,
% including relations for debugging or extra relations as you desire.
% All should be included when you turn this in.  Your rules must be able
% to work on any data and across as many generations as the data specifies.
% They may not be specific to this data.

% Using SWI-Prolog, run your code, demonstrating that it works in all modes.
% Log this session and turn it in with your code in this (modified) file.
% You examples should demonstrate working across 4 generations where
% applicable.

% Fact recording Predicates:

% list of two parents, father first, then list of all children
% parent_list(?Parent_list, ?Child_list).

% Data:

parent_list([fred_smith, mary_jones],
            [tom_smith, lisa_smith, jane_smith, john_smith]).

parent_list([tom_smith, evelyn_harris],
            [mark_smith, freddy_smith, joe_smith, francis_smith]).

parent_list([mark_smith, pam_wilson],
            [martha_smith, frederick_smith]).

parent_list([freddy_smith, connie_warrick],
            [jill_smith, marcus_smith, tim_smith]).

parent_list([john_smith, layla_morris],
            [julie_smith, leslie_smith, heather_smith, zach_smith]).

parent_list([edward_thompson, susan_holt],
            [leonard_thompson, mary_thompson]).

parent_list([leonard_thompson, lisa_smith],
            [joe_thompson, catherine_thompson, john_thompson, carrie_thompson]).

parent_list([joe_thompson, lisa_houser],
            [lilly_thompson, richard_thompson, marcus_thompson]).

parent_list([john_thompson, mary_snyder],
            []).

parent_list([jeremiah_leech, sally_swithers],
            [arthur_leech]).

parent_list([arthur_leech, jane_smith],
            [timothy_leech, jack_leech, heather_leech]).

parent_list([robert_harris, julia_swift],
            [evelyn_harris, albert_harris]).

parent_list([albert_harris, margaret_little],
            [june_harris, jackie_harrie, leonard_harris]).

parent_list([leonard_harris, constance_may],
            [jennifer_harris, karen_harris, kenneth_harris]).

parent_list([beau_morris, jennifer_willis],
            [layla_morris]).

parent_list([willard_louis, missy_deas],
            [jonathan_louis]).

parent_list([jonathan_louis, marsha_lang],
            [tom_louis]).

parent_list([tom_louis, catherine_thompson],
            [mary_louis, jane_louis, katie_louis]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% SWE1 Assignment - Create rules for:

%% Check member of child list (predicate given in lecture)
% parent(?Parent, ?Child).
parent(Parent,Child) :- parent_list(ParentList,ChildList), member(Parent,ParentList), member(Child, ChildList).

%% Essentially the same as parent, just check if both a member of a single parent list
% married(?Husband, ?Wife).
married(Husband,Wife) :- parent_list(ParentList,_), member(Husband,ParentList), member(Wife, ParentList), (Husband \== Wife).

%% Added in helper predicate ancestor count which keeps track of recursion. Will be used in cousin_type
% ancestor_cnt(?Ancestor, ?Person, N).
ancestor_cnt(Ancestor,Person, N) :- N is 1, parent(Ancestor, Person).
ancestor_cnt(Ancestor,Person, N) :- parent(Ancestor, ChildOfAncestor), ancestor_cnt(ChildOfAncestor, Person, N2), N is N2+1.

%% Wrapper call ignoring count
% ancestor(?Ancestor, ?Person).
ancestor(Ancestor, Person) :- ancestor_cnt(Ancestor,Person, _).

%% Check children and children's children
% descendent(?Decendent, ?Person).
descendent(Descendent,Person) :- parent(Person, Descendent).
descendent(Descendent,Person) :- parent(Person, Grandchild), descendent(Descendent, Grandchild).

%% Check if ancestor is an ancestor of person 1 and 2
% common_ancestor(?Person1, ?Person2, ?Ancestor).
common_ancestor(Person1, Person2, Ancestor) :- ancestor(Ancestor, Person1), ancestor(Ancestor, Person2).

%% Check if descendants of one another or have a common ancestor
% blood(?Person1, ?Person2). %% blood relative
blood(Person1, Person2) :- descendent(Person1, Person2).
blood(Person1, Person2) :- descendent(Person2, Person1).
blood(Person1, Person2) :- common_ancestor(Person1, Person2, _).

%% Check if both belong to same child list and exclude same person (basically married)
% sibling(?Person1, Person2).
sibling(Person1, Person2) :- parent_list(_,ChildList), member(Person1, ChildList), member(Person2, ChildList), (Person1 \== Person2).

%% Check first element of parent node in parent list of child
% father(?Father, ?Child).
father(Father, Child) :- parent_list([Father|_], ChildList), member(Child, ChildList).

%% Check second element of parent node in parent list of child
% mother(?Mother, ?Child).
mother(Mother, Child) :- parent_list([_|[Mother|_]],ChildList), member(Child, ChildList).

%% Obtained from announcement discussion board
% lca(?Person1, Person2, ?Ancestor).
lca(P1,P2,A) :- father(A,P1), father(A,P2), (P1 \== P2).
lca(P1,P2,A) :- father(A,P1), father(A,P4), (P1 \== P4), ancestor(P4, P2).
lca(P1,P2,A) :- father(A,P3), ancestor(P3,P1), father(A,P2), (P3 \== P2).
lca(P1,P2,A) :- father(A,P3), ancestor(P3,P1), father(A,P4), (P3 \== P4), ancestor(P4, P2).

%% Father of first cousins
% uncle(?Uncle, ?Person). 
uncle(Uncle,Person) :- parent_list([Uncle|_], ChildList), father(Father, Person), father(Grandfather, Uncle), father(Grandfather, Father), not(member(Person,ChildList)).

%% Mothers of first cousins
% aunt(?Aunt, ?Person). 
aunt(Aunt,Person) :- parent_list([_|[Aunt|_]], ChildList), father(Father, Person), father(Grandfather, Aunt), father(Grandfather, Father), not(member(Person,ChildList)).

%%Wrapper call for cousin_type with null type and removed
% cousin(?Cousin, ?Person).
cousin(Cousin,Person) :- cousin_type(Cousin,Person,_,_).

%% 1st cousin, 2nd cousin, 3rd once removed, etc.
%% Logic for cousin type and removed from announcement discussion board
% cousin_type(+Person1, +Person2, -CousinType, -Removed).
cousin_type(Person1, Person2, CousinType, Removed) :- lca(Person1, Person2, LCA), ancestor_cnt(LCA, Person1, D1), ancestor_cnt(LCA, Person2, D2), D1 >= 2, D2 >= 2, CousinType is (min(D1,D2)-1), Removed is abs(D1-D2).
