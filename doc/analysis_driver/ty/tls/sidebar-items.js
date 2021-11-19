initSidebarItems({"fn":[["enter_context","Sets `context` as the new current `ImplicitCtxt` for the duration of the function `f`."],["with","Allows access to the `TyCtxt` in the current `ImplicitCtxt`. Panics if there is no `ImplicitCtxt` available."],["with_context","Allows access to the current `ImplicitCtxt`. Panics if there is no `ImplicitCtxt` available."],["with_context_opt","Allows access to the current `ImplicitCtxt` in a closure if one is available."],["with_opt","Allows access to the `TyCtxt` in the current `ImplicitCtxt`. The closure is passed None if there is no `ImplicitCtxt` available."],["with_related_context","Allows access to the current `ImplicitCtxt` whose tcx field is the same as the tcx argument passed in. This means the closure is given an `ImplicitCtxt` with the same `'tcx` lifetime as the `TyCtxt` passed in. This will panic if you pass it a `TyCtxt` which is different from the current `ImplicitCtxt`’s `tcx` field."]],"struct":[["ImplicitCtxt","This is the implicit state of rustc. It contains the current `TyCtxt` and query. It is updated when creating a local interner or executing a new query. Whenever there’s a `TyCtxt` value available you should also have access to an `ImplicitCtxt` through the functions in this module."]]});