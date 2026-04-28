append([], X, X).
append([T|X], Y, [T|Z]) :- append(X, Y, Z).
len([], X) :- X = 0.
len([T|X], N) :- len(X, N0), N = N0 + 1.
loop1([], [], X, _) :- X = 0.
loop1(A, B, I, N) :- I > 0, I0 = I - 1, loop2(A1, N), loop3(B1, I), 
    loop1(A0, B0, I0, N), append(A1, A0, A), append(B1, B0, B).
loop2([], X) :- X = 0.
loop2(A, J) :- J > 0, J0 = J - 1, loop2(A0, J0), append(A0, [Z], A), Z = 0.
loop3([], X) :- X = 0.
loop3(B, J) :- J > 0, J0 = J - 1, loop3(B0, J0), append(B0, [Z], B), Z = 0.
incorrect :- loop1(A, B, X, Y), len(A, Na), len(B, Nb), Na < Nb, Y > 0, X = Y.