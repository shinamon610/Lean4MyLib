namespace MyState
def exec [Monad M](state:StateT S M A) (init:S):M S:= (state.run init) <&> fun (_,s) => s
def execD [Monad M][Inhabited S](state:StateT S M A):M S:= (state.run default) <&> fun (_,s) => s
def empty [Monad M]:StateT S M Unit := return ()
