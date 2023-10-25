open Ex3
open util/ordering[Id] 


sig Id {} 

// Define OrderedNode signature
sig OrderedNode extends Node {
  id: one Id
}


fact OrderedNodesInAscendingOrder {
  // Ensure nodes are arranged in ascending order based on their "id"
  all o1, o2: OrderedNode | o1 != o2 && o1.nnext = o2 implies o1.id.lt[o2.id]
}

run {} for exactly 2 HeadNode, exactly 5 OrderedNode, exactly 5 Id, exactly 0 Node 