8/5
- 2 programs: abstract and experiment. Both take `model : <G,F>` as an input and have `dag_fun_compatible` for well-formedness.
- abstract input:
    - a model;
    - a distr over context;
        - ps: even though it's a joint distr, context nodes are indep by def, so it's the same as the product of marginals.
        - then we can infer a unique distr over the world
            this is called a `pushforward of P_cont`, which is a deterministic function applied to P_cont
        - Then we can marginalize to get P(response|do(treatment))
    - a sequence of operations that transforms the model and thus the distribution
        - it transforms `model`, which yields a new `P`
        - TBD: does it transform `P` directly? or is that the job of experiment?
- experiment input:
    - a model;
    - a sequence of units (?) of size n (?) with concrete values (?)

- probability specific
    - each node's domain can have it's own finType
