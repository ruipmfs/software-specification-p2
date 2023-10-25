open Ex3
open util/ordering[Id] 


sig Id {} 

// Define OrderedNode signature
sig OrderedNode extends Node {
  id: one Id
}


fact OrderedNodesInAscendingOrder {
  // Ensure nodes are arranged in ascending order based on their "id"
  always all o1, o2: OrderedNode | o1 != o2 && o1.nnext = o2 implies o1.id.lt[o2.id]
}

fact AllNodesBelongToDoublyLinkedList {
  //All nodes belong to one doubly-linked list
  always all n: Id |  n in (OrderedNode.id)
}

fact DistinctFrstAndLst {
  // Ensures that diferent HeadNodes are pointing to different lists
  always all dl1, dl2: OrderedNode | dl1 != dl2  implies dl1.id != dl2.id
}

//Ex 4.2
run { #HeadNode >= 2 && #Node >= 5 } for 6