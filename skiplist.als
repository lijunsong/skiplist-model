open util/ordering[Time]
open util/ordering[Value]
open util/ternary

sig Value {}
sig N in Value {}
fact { N = Value - first - last }

sig Time {}

sig Node {
	succs: (seq Node) -> Time,
	key: Value,
}

one sig HeadNode extends Node {} {
	key = first
}


one sig TailNode extends Node {} {
	no succs
	key = last
}

abstract sig Operation {}
abstract sig Add extends Operation {}
one sig AddRestart extends Add {}
one sig AddFind extends Add {}
one sig AddLock extends Add {}
one sig AddUnlock extends Add {}

abstract sig Del extends Operation {}
one sig DelRestart extends Del {}
one sig DelFind extends Del {}
one sig DelLock extends Del {}
one sig DelUnlock extends Del {}

sig Thread {
	op: Operation lone ->Time,
	arg: N,
	height: Int,
	find: Node->Int->Node->Time
} {
  // TODO: constrain the height to the height of HeadNode
	height >= 0 and height <= max[HeadNode.succs.first.Node]
}

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
	//all t: Time, n: Node - nodes.t | no owns.t.n
}

fun succsAtLevel(lv: Int, t: Time): set Node->Node {
	{x: Node, y: Node | x->lv->y->t in succs}
}

fun nodesAtLevelLess(x: Value, lv: Int, t: Time): set Node {
	{n: SkipList.nodes.t | n in HeadNode.*(succsAtLevel[lv, t]) and n.key in prevs[x]}
}

fun valuePreds(x: Value, lv: Int, t: Time): seq Node {
	{lv': Int, n: SkipList.nodes.t | lv' <= lv and lv' >= 0 and n.key = max[nodesAtLevelLess[x, lv', t].key]}
}

fun succsOfPreds(predNodes: seq Node, t: Time): set Int -> Node {
	{lv: predNodes.Node, n: Node | (lv.predNodes)->lv->n in succs.t} 
}

fun outerJoin(left, right: seq Node): set Node -> Int -> Node {
	{l: Node, lv: Int, r: Node | lv->l in left and lv->r in right}
}

pred emptyList {
	no owns.first
	succs.first = HeadNode->(0+1+2+3)->TailNode
}

pred smallList {
	some disj n1, n2, n3: Node - HeadNode - TailNode {
    // headnode < n1 < n2 < n3 < tailnode
		HeadNode->2->TailNode + HeadNode->1->n2 + n2->1->TailNode 
			+ HeadNode->0->n1 + n1->0->n2 + n2->0->n3 + n3->0->TailNode + HeadNode->3->TailNode
     = succs.first

    lt[n1.key, n2.key] and lt[n2.key, n3.key]
    n3.key != n2.key and n2.key != n1.key
    (n1+n2+n3).key in N
		//some v1: N | v1 not in (n1+n2+n3).key and lt[v1,n3.key] and lt[n2.key, v1]
  }
}

pred threadNoChange(t,t': Time, thr: Thread) {
    thr.op.t = thr.op.t'
    thr.find.t = thr.find.t'
}
pred threadsNoChange(t,t': Time) {
//    Thread.op.t = Thread.op.t'
//    Thread.find.t = Thread.find.t'
    all thr: Thread | threadNoChange[t,t',thr]
}
pred noThreadsChangeExcept(t,t': Time, thr: Thread) {
    all thrs: Thread-thr | threadNoChange[t,t',thrs]
//    (Thread-thr).op.t = (Thread-thr).op.t'
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
    no thr.op.t'
    no thr.find.t'
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
    thr.find.t.Node.Int = thr.(SkipList.owns.t)
}

pred atomAdd(t,t': Time, thr: Thread) {
	some n: Node - SkipList.nodes.t {
		n.key = thr.arg
		let xPreds = valuePreds[thr.arg, thr.height, t] {
			//(~xPreds)->n->t' in succs // Link predecessors
			let xSuccs = succsOfPreds[xPreds, t] {
			//	n->xSuccs->t' in succs // Link successors
				succs.t + n->xSuccs + (~xPreds)->n - outerJoin[xPreds, xSuccs] = succs.t'
				SkipList.nodes.t' = SkipList.nodes.t + n
			}
		}
	}
  thr.find.t = thr.find.t'
  noThreadsChangeExcept[t,t',thr]
  SkipList.owns.t = SkipList.owns.t'
}

pred atomDel(t, t': Time, thr: Thread) {
	atomAdd[t', t, thr]
}

/* this function returns one predecessor node that is not locked by thread thr.
 * it first gets the predecessor at each level {0->node1, 1->node2, 3->headnode}.
 * Then filter out the level that has been locked by thr.
 * Finally return the node mapped by minimum int.
 */
fun nextNodeToLock(t: Time, thr: Thread) : Node {
    let allPredsNode = ~(thr.find.t.Node) { // type: Int->Node
        let nextUnlockedNodeSeq = allPredsNode - allPredsNode:>SkipList.owns.t[thr] {
            let num = min[nextUnlockedNodeSeq.Node] {
                num.nextUnlockedNodeSeq
            }
        }
    }
}
fun nextNodeToUnlock(t: Time, thr: Thread) : Node {
    let allPredsNode = ~(thr.find.t.Node) { // type: Int->Node
        let nextLockedNodeSeq = allPredsNode :> SkipList.owns.t[thr] {
            let num = min[nextLockedNodeSeq.Node] {
                num.nextLockedNodeSeq
            }
        }
    }
}

pred atomLockOneNode(t,t': Time, thr: Thread) {
    // locking successfully or getting blocked should depend on
    // SkipList.owns at time t.
    let node = nextNodeToLock[t, thr] {
        no SkipList.owns.t.node 
        skipListNoChangeExceptAddLock[t,t',thr,node]
        threadsNoChange[t,t']
    }
}

pred atomUnlockOneNodeThenFinish(t,t': Time, thr: Thread) {
    let n = nextNodeToUnlock[t, thr] {
        some n implies {
            skipListNoChangeExceptRemoveLock[t,t',thr,n]
            threadsNoChange[t,t']
        } else {
            no thr.op.t'
            no thr.find.t'
            noThreadsChangeExcept[t,t',thr]
            skipListNoChange[t,t']
        }
    }
}

pred atomUnlockOneNode(t,t': Time, thr: Thread) {
    let n = nextNodeToUnlock[t, thr] {
        some n 
        skipListNoChangeExceptRemoveLock[t,t',thr,n]
        threadsNoChange[t,t']
    }
}

/* given a Value, this function will return the predecessors->successors info of
 * the value x. (NOTE: x should not in the list)
 */
fun predsAndSuccs(t: Time, thr: Thread): Node->Int->Node {
    let p = valuePreds[thr.arg, thr.height, t] |
        let s = succsOfPreds[p, t] |
           outerJoin[p, s]
}
/* For doc: for a thread that should be blocked at time t', we can not explicitly
 * offer an idle state for thread. We want doNextAddOp to be false and 
 * the trace will select other instances satisfying doNextAddOp, and thus no
 * consecutive states are the same.
 */

/* TODO: (maybe assert) thr1, th2 both add value1. thr1 step to AddLock at t1, thr2 
 * step to AddLock at t2. thr1 add value1 at t3, and thr2 add value1 at t4. Now 
 * multiple value1s exist in the list! */
pred doNextAddOp(t,t': Time, thr: Thread) {
    thr.op.t = AddFind implies {
        isValueInList[t, thr.arg] implies 
            threadFinishesDirectly[t, t', thr]
        else {
            thr.op.t' = AddLock
            skipListNoChange[t,t']
            noThreadsChangeExcept[t,t',thr]
            thr.find.t' = predsAndSuccs[t, thr]
        }
    } else thr.op.t = AddLock implies {
        areAllPredsLockedBy[t, thr] implies {
            // if all preds are locked by thr, validate the preds->succs             
            predsAndSuccs[t, thr] = thr.find.t implies {
                // preds->succs do not change, the thread is safely to add things
                atomAdd[t, t', thr]
								thr.op.t' = AddUnlock
            } else {
                thr.op.t' = AddRestart
                thr.find.t' = thr.find.t
                noThreadsChangeExcept[t,t',thr]
                skipListNoChange[t,t']
            }
        } else 
            atomLockOneNode[t,t',thr]
    } else thr.op.t = AddUnlock implies {
        some thr.(SkipList.owns.t) implies 
            atomUnlockOneNode[t,t',thr] 
        else 
            threadFinishesDirectly[t,t',thr]
    } else {
        // restart
        thr.op.t = AddRestart
        some thr.(SkipList.owns.t) implies
            atomUnlockOneNode[t,t',thr]
        else {
            // no nodes can be unlocked
            thr.op.t' = AddFind
            no thr.find.t'
            noThreadsChangeExcept[t,t',thr]
            skipListNoChange[t,t']
        }
    }
}

pred doNextDelOp(t, t': Time, thr: Thread) {
		thr.op.t = DelFind implies {
				not isValueInList[t, thr.arg] implies
						threadFinishesDirectly[t, t', thr]
				else {
						thr.op.t' = DelLock
						skipListNoChange[t, t']
						noThreadsChangeExcept[t, t', thr]
						thr.find.t' = predsAndSuccs[t, thr]
				}
		} else thr.op.t = DelLock implies {
				areAllPredsLockedBy[t, thr] implies {
						predsAndSuccs[t, thr] = thr.find.t implies {
								atomDel[t, t', thr]
								thr.op.t' = DelUnlock
						} else {
								thr.op.t' = DelRestart
                thr.find.t' = thr.find.t // keep the find info for unlocking
                noThreadsChangeExcept[t,t',thr]
                skipListNoChange[t,t']
						}
				} else
						atomLockOneNode[t, t', thr]
		} else thr.op.t = DelUnlock implies {
        some thr.(SkipList.owns.t) implies 
            atomUnlockOneNode[t,t',thr] 
        else 
            threadFinishesDirectly[t,t',thr]
		} else {
        // restart
        thr.op.t = DelRestart
        some thr.(SkipList.owns.t) implies
            atomUnlockOneNode[t,t',thr]
        else {
            // no nodes can be unlocked
            thr.op.t' = DelFind
            no thr.find.t'
            noThreadsChangeExcept[t,t',thr]
            skipListNoChange[t,t']
        }
    }
}

pred allFinishes(t,t': Time) {
    no Thread.op.t
    no Thread.find.t
    threadsNoChange[t,t']
    skipListNoChange[t,t']
}

pred trace {
    // 866020->372100
    all t: Time-last | some thrs: Thread | let t' = t.next { // TODO: diff to say one thr: Thread
        allFinishes[t,t'] or {
           all thr: thrs | // writing in this way can significantly reduce variables.
              (thr.op.t in Add and doNextAddOp[t,t',thr]) or
              (thr.op.t in Del and doNextDelOp[t,t',thr])
        }
    }
}

fact init {
    /* no thread owns locks at beginning */
    no owns.first
    /* all thread should start from find */
    no Thread.find.first
    all thr: Thread | thr.op.first = AddFind or thr.op.first = DelFind
}

/* IMPORTANT: 
 * 1. make sure the scopes for Value,Node,Thread are matched! 
 * 2. use exactly to reduce variables and clauses whenever possible!
 * */
run { 
    smallList
    some thr: Thread | thr.arg not in SkipList.nodes.first.key
    some thr: Thread, t:Time-last | thr.op.t = AddRestart
} for exactly 2 Thread, exactly 15 Time, exactly 6 Value, exactly 6 Node

run {
	smallList
  // one thread does add
  one thr: Thread | thr.op.first = AddFind and thr.arg not in SkipList.nodes.first.key
                    and thr.height >= 2
  // one thread does del
  one thr: Thread | some t: Time-last | thr.op.first = DelFind and thr.op.t = DelLock

  all disj thr1,thr2: Thread | thr1.arg != thr2.arg

  all t: Time-last | some Thread.op.t
  
} for exactly 3 Thread, exactly 24 Time, exactly 10 Value, exactly 7 Node

pred noDuplicatesProperty {
  all t: Time | all disj n1, n2: SkipList.nodes.t | n1.key != n2.key
}

pred mutualExclusionProperty {
  all t: Time | all n: SkipList.nodes.t | lone owns.t.n
}

pred SkipListProperty {
	all t: Time, lv2, lv1: Int |
		lv1 >= 0 and lv2 >= lv1 implies lv2.(Node.succs.t) in lv1.(Node.succs.t)
}

pred SkipListInOrderProperty{
	all t: Time, r: succsAtLevel[0,t] |
		lt[r.Node.key, (Node.r).key]
}

pred AcyclicProperty {
	//all t: Time, n: Node | n not in n.^(select13[succs.t])
	//all n: Node | n not in n.^(select13[succs.Time])
	no ^(select13[succs.Time]) & iden
}

pred SomeDeletionOfLockedNodes {
	some t: Time | some disj thr1, thr2: Thread | some n: SkipList.nodes.t {
		thr1->n->t in SkipList.owns
		thr2.op.t = DelLock
		thr2.arg = n.key
		thr2.op.(t.next) = DelUnlock
	}
}

// TODO: what will happen if a thread is trying to delete a locked node?
// one thread cannot unlock other threads' lock
pred CanUnlockOtherThreadsLock {
    some t: Time | some disj thrToUnlock, thrHoldingLock : Thread {
        let ns = nextNodeToUnlock[t,thrToUnlock] {
            thrToUnlock.op.t = AddUnlock
            thrHoldingLock.op.t = AddLock
            // thrHoldingLock holds the lock of the predecessors in its 'find' field
            ns in (thrHoldingLock.find.t).Node.Int
        }    
    }
}
assert ShouldNotUnlockOthersLock {
    emptyList => not CanUnlockOtherThreadsLock
}
// we need two types of assertion: one on the skiplist property; another is on our model.
// restart state has cleaned everything.
pred restartButNotClean {
    some t: Time | some thr: Thread {
        thr.op.t = AddFind or thr.op.t = DelFind
        some thr.find.t or some SkipList.owns.t[thr]
    }
}

assert restartWithCleanState {
    emptyList => not restartButNotClean
}

check restartWithCleanState
for exactly 3 Thread, exactly 10 Time, exactly 5 Value, exactly 5 Node

run {smallList and SomeDeletionOfLockedNodes }
for exactly 2 Thread, exactly 15 Time, exactly 5 Value, exactly 5 Node


assert NoDuplicates {
	emptyList => noDuplicatesProperty
}

assert ThreadsMutualExclusive {
	emptyList => mutualExclusionProperty
}

assert SkipListInOrder {
	emptyList => SkipListInOrderProperty
}

assert SkipListP {
	emptyList => SkipListProperty
}

assert Acyclic {
	emptyList => AcyclicProperty
}

check NoDuplicates for exactly 2 Thread, exactly 10 Time, exactly 5 Value, exactly 5 Node

check ThreadsMutualExclusive for exactly 2 Thread, exactly 10 Time, exactly 5 Value, exactly 5 Node

check SkipListP for exactly 2 Thread, exactly 10 Time, exactly 5 Value, exactly 5 Node

check SkipListInOrder for exactly 3 Thread, exactly 10 Time, exactly 5 Value, exactly 5 Node

check Acyclic for exactly 2 Thread, exactly 10 Time, exactly 5 Value, exactly 5 Node
