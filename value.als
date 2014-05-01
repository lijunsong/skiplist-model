module value

abstract sig Value {
	predv: set Value
} {
	@predv.@predv in @predv
    all v, w: Value | v in w.@predv and w in v.@predv implies v = w
	all v, w: Value | v in w.@predv or w in v.@predv
}

one sig Infty extends Value {} {
	predv = Value
}
one sig NInfty extends Value {} {
	one predv
}

sig Fin extends Value {}

fun maxVal(x: set Value): set Value {
	x - (~predv - iden).x
}
