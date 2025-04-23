namespace MyState
def exec [Monad M](state:StateT S M A) (init:S):M S:= (state.run init) <&> fun (_,s) => s
def empty [Monad M]:StateT S M Unit := return ()
