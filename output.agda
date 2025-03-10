H_0→1 : p , state0 —→ state1 , t0
H_0→1  = step-Add p state0 (s≤s z≤n) refl

sentry_H_0→1 : t0 , p , state0 —→ state1
sentry_H_0→1 = step-Add t0 p state0 (s≤s z≤n) refl

H_1→2 : p , state1 —→ state2 , t1
H_1→2 = step-Add p state1 (s≤s (s≤s z≤n)) refl

sentry_H_1→2 : t1 , p , state1 —→ state2
sentry_H_1→2 = step-Add t1 p state1 (s≤s (s≤s z≤n)) refl

H_2→3 : p , state2 —→ state3 , t2
H_2→3 = step-Add p state2 (s≤s (s≤s (s≤s z≤n))) refl

sentry_H_2→3 : t2 , p , state2 —→ state3
sentry_H_2→3 = step-Add t2 p state2 (s≤s (s≤s (s≤s z≤n))) refl

H_3→*3 : p , state3 —→* state3 , emptyTrace
H_3→*3 = done p state3

sentry_H_3→*3 : emptyTrace , p , state3 —→* state3
sentry_H_3→*3 = done emptyTrace p state3
