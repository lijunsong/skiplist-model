open util/ordering[Time]
open value

sig Time {}

sig Node {
	succs: (seq Node) -> Time,
	key: Value
}

one sig HeadNode extends Node {} {
	key = NInfty
	//all t: Time | #(succs.t) = 5
	@key.NInfty = this
}


one sig TailNode extends Node {} {
	key = Infty
	no succs
	@key.Infty = this
}

abstract sig Operation {}
abstract sig Add extends Operation {}
one sig AddFind extends Add {}
one sig AddLock extends Add {}
one sig AddUnlock extends Add {}

sig Thread {
    op: Operation lone ->Time,
    arg: Value
} { NInfty not in arg and Infty not in arg }

one sig SkipList {
	nodes: set Node->Time,
  // which thread locks which nodes at which level at which time
	owns: Thread->Node->Time
} {
	all t: Time | HeadNode in nodes.t
	all t: Time | TailNode in nodes.t
	// Nodes that aren't in the list are NOT in the list: TODO: bug nodes include nodes not in list
	all t: Time, n: Node - nodes.t | no n.succs.t and no succs.t.n
  all t: Time, notTail: nodes.t-TailNode, notHead: nodes.t-HeadNode
       | some notTail.succs.t and some succs.t.notHead
	// At most one owner of a locked node
	//all t: Time, n: nodes.t | lone owns.t.n
	// No locking nodes not in list...
	all t: Time, n: Node - nodes.t | no owns.t.n
}

fun succsAtLevel(lv: Int, t: Time): set Node->Node {
	{x: Node, y: Node | x->lv->y->t in succs}
}

fun nodesAtLevelLess(x: Value, lv: Int, t: Time): set Node {
	{n: SkipList.nodes.t | n in HeadNode.*(succsAtLevel[lv, t]) and n.key in x.predv}
}

fun valuePreds(x: Value, lv: Int, t: Time): seq Node {
	{lv': Int, n: SkipList.nodes.t | lv' <= lv and lv' >= 0 and n.key = maxVal[nodesAtLevelLess[x, lv', t].key]}
}

pred smallList {
	some disj n1, n2, n3: Node - HeadNode - TailNode | 
		HeadNode->2->TailNode + HeadNode->1->n2 + n2->1->TailNode 
			+ HeadNode->0->n1 + n1->0->n2 + n2->0->n3 + n3->0->TailNode + HeadNode->3->TailNode
     = succs.first
		and
		n3.key->n2.key + n2.key->n1.key in predv
		and n3.key != n2.key and n2.key != n1.key
		and some v1: Fin | v1 not in (n1+n2+n3).key and n3.key->v1 + v1->n2.key in predv
}

pred threadNoChange(t,t': Time, thr: Thread) {
    thr.op.t = thr.op.t'
}
pred threadsNoChange(t,t': Time) {
    all thr: Thread | threadNoChange[t,t',thr]
}
pred noThreadsChangeExcept(t,t': Time, thr: Thread) {
    all thrs: Thread-thr | threadNoChange[t,t',thrs]

}
pred skipListNoChange(t, t': Time) {
    SkipList.nodes.t = SkipList.nodes.t'
    SkipList.owns.t = SkipList.owns.t'
    succs.t = succs.t'
}
pred skipListNoChangeExceptAddLock(t,t': Time, thr: Thread, n: Node) {
    SkipList.nodes.t = SkipList.nodes.t'
    succs.t = succs.t'
    SkipList.owns.t' = SkipList.owns.t + thr->n
}
pred skipListNoChangeExceptRemoveLock(t,t': Time, thr: Thread, n: Node) {
    SkipList.nodes.t = SkipList.nodes.t'
    succs.t = succs.t'
    SkipList.owns.t' = SkipList.owns.t - thr->n
}

pred threadFinishesDirectly(t,t': Time, thr: Thread) {
    -- post
    some thr.op.t and no thr.op.t'
    -- frame
    noThreadsChangeExcept[t, t', thr]
    skipListNoChange[t, t']
}

pred isValueInList(t: Time, x: Value) {
    let nodes = SkipList.nodes.t {
        x in nodes.key
    }
}

pred areAllPredsLockedBy(t: Time, thr: Thread) {
    let nodes = valuePreds[thr.arg, 2, t] {
        Int.nodes = thr.(SkipList.owns.t)
    }
}

pred atomAddAndUnlock(t,t': Time, thr: Thread) {
}

/* this function returns one predecessor node that is not locked by thread thr.
 * it first gets the predecessor at each level {0->node1, 1->node2, 3->headnode}.
 * Then filter out the level that has been locked by thr.
 * Finally return the node mapped by minimum int.
 */
fun nextNodeToLock(t: Time, thr: Thread) : Node {
    let allPredsNode = valuePreds[thr.arg, 2, t] |
        let nextUnlockedNodeSeq = allPredsNode - allPredsNode:>SkipList.owns.t[thr] {
            let num = min[nextUnlockedNodeSeq.Node] {
                num.nextUnlockedNodeSeq
            }
        }
}

pred atomLockOneNode(t,t': Time, thr: Thread) {
    // locking successfully or getting blocked should depend on
    // SkipList.owns at time t.
    let node = nextNodeToLock[t, thr] {
        some SkipList.owns.t.node implies {
            // another thread holds the lock, this thread is blocked from t->t'
            // TODO: this frame condition results in two states the same.
            threadsNoChange[t,t']
            skipListNoChange[t,t']
        } else {// the thread gets the lock
            skipListNoChangeExceptAddLock[t,t',thr,node]
            threadsNoChange[t,t']
        }
    }
}

pred atomUnlockAndFinish(t,t': Time, thr: Thread) {
    all n: thr.(SkipList.owns.t) | skipListNoChangeExceptRemoveLock[t,t',thr, n]
    thr.op.t = AddUnlock
    no thr.op.t'
}

pred doNextAddOp(t,t': Time, thrs: Thread) {
    all thr: thrs |
    thr.op.t = AddFind implies {
        thr.op.t' = AddLock
        isValueInList[t, thr.arg] implies 
            threadFinishesDirectly[t, t', thr]
        else {
            skipListNoChange[t,t']
            noThreadsChangeExcept[t,t',thr]
        }
    } else thr.op.t = AddLock implies {
        // NOTE: thr.op.t' is not necessarily changed to Unlock
        // thr.op.'t should be changed to addUnlock in this case
        areAllPredsLockedBy[t, thr] implies
            //atomAddAndUnlock[t, t', thr]
            atomUnlockAndFinish[t,t',thr]
        else 
            atomLockOneNode[t,t',thr]
    } /*else thr.op.t = AddUnlock implies {
        atomUnlockAndFinish[t,t',thr]
    } */
}

pred isThreadFinished(t: Time, thr: Thread) {
    no thr.op.t
}

pred trace {
    all t: Time-last | some thr: Thread | let t' = t.next {
        // TODO just trace some thr which are not finished.
        isThreadFinished[t, thr] implies 
            skipListNoChange[t, t'] and threadNoChange[t,t',thr]
        else 
            doNextAddOp[t, t', thr]
    }
}

pred init {
    /* no thread owns locks at beginning */
    no owns.first
    /* all thread should start from find */
    all thr: Thread | thr.op.first = AddFind
    /* customized */
    smallList
    some thr: Thread | thr.arg not in SkipList.nodes.first.key   
}

run { 
    init[]
    trace[]
} for 6 but exactly 3 Thread, exactly 15 Time, exactly 10 Value


run { smallList } for 7 but 2 Thread




