module red_black_map::binary_search_tree {

    use std::vector;


    const NIL: u64 = 0xffffffffffffffff;

    const LEFT: u64 = 0;
    const MINIMUM: u64 = 0;

    const RIGHT: u64 = 1;
    const MAXIMUM: u64 = 1;

    /// Map key already exists.
    const E_KEY_ALREADY_EXISTS: u64 = 0;

    struct Node {
        key: u32,
        parent: u64,
        children: vector<u64>
    }

    spec Node {
        invariant len(children) == 2;
    }

    struct Map {
        root: u64,
        nodes: vector<Node>
    }

    spec module {
        pragma verify = true;
    }

    spec Map {
        invariant len(nodes) < NIL;
        invariant root == NIL <==> len(nodes) == 0;
        invariant root != NIL ==> root >= 0 && root < len(nodes);

        invariant (forall idx: num where idx >= 0 &&  idx < len(nodes): 
            nodes[idx].children[LEFT] != NIL ==> nodes[idx].children[LEFT] < len(nodes)) &&
        (forall idx: num where idx >= 0 &&  idx < len(nodes): 
            nodes[idx].children[RIGHT] != NIL ==> nodes[idx].children[RIGHT] < len(nodes));  
        invariant forall idx: num where idx >= 0 && idx < len(nodes): 
            nodes[idx].parent != NIL ==> nodes[idx].parent < len(nodes);  
        invariant forall idx: num where idx >= 0 && idx < len(nodes):
            idx != nodes[idx].parent;  
        invariant forall idx: num where idx >= 0 && idx < len(nodes):
            idx != nodes[idx].children[LEFT];  
        invariant forall idx: num where idx >= 0 && idx < len(nodes):
            idx != nodes[idx].children[RIGHT];             
        invariant forall idx: num where idx >= 0 && idx < len(nodes):
            nodes[idx].children[LEFT] != NIL ==> idx < nodes[idx].children[LEFT];  
        invariant forall idx: num where idx >= 0 && idx < len(nodes):
            nodes[idx].children[RIGHT] != NIL ==> idx < nodes[idx].children[RIGHT];     
        invariant forall idx: num where idx >= 0 && idx < len(nodes):
            diff_subtree(nodes, idx);                                                                          
        invariant forall idx_1: num, idx_2: num where idx_1 >= 0 && idx_1 < len(nodes) && idx_2 >= 0 && idx_2 < len(nodes) && idx_1 != idx_2: 
            nodes[idx_1].children[LEFT] != NIL ==> 
                         (nodes[idx_2].children[LEFT] != nodes[idx_1].children[LEFT]) &&  
                         (nodes[idx_2].children[RIGHT] != nodes[idx_1].children[LEFT]);
        invariant forall idx_1: num, idx_2: num where idx_1 >= 0 && idx_1 < len(nodes) && idx_2 >= 0 && idx_2 < len(nodes) && idx_1 != idx_2: 
            nodes[idx_1].children[RIGHT] != NIL ==> 
                         (nodes[idx_2].children[LEFT] != nodes[idx_1].children[RIGHT]) &&  
                         (nodes[idx_2].children[RIGHT] != nodes[idx_1].children[RIGHT]);     
        invariant forall idx: num where idx >= 0 && idx < len(nodes): 
            nodes[idx].parent != NIL ==> (nodes[nodes[idx].parent].children[LEFT] == idx || nodes[nodes[idx].parent].children[RIGHT] == idx);                           
    }

    public fun new(): Map {
        Map { root: NIL, nodes: vector[] }
    }
    spec new {
        ensures len(tset(result, result.root)) == 0;
    }

    spec fun tset(self: Map, cur_idx: u64): vector<u32> {
     if (cur_idx == NIL) {
         vector[]
     } else {
         concat(vector[self.nodes[cur_idx].key], concat(tset(self, self.nodes[cur_idx].children[LEFT]), tset(self, self.nodes[cur_idx].children[RIGHT])))
     }
    }

    spec fun contains(self: Map, cur_idx: u64, key: u32): bool {
     if (cur_idx == NIL) {
         false
     } else {
         if (self.nodes[cur_idx].key == key) {
            true
         } else if (key < self.nodes[cur_idx].key) {
            contains(self, self.nodes[cur_idx].children[LEFT], key)
         } else {
            contains(self, self.nodes[cur_idx].children[RIGHT], key)           
         }
     }
    }

    spec fun tset_size(self: Map, cur_idx: u64): u64 {
     if (cur_idx == NIL) {
         0
     } else {
        1 + tset_size(self, self.nodes[cur_idx].children[LEFT]) + tset_size(self, self.nodes[cur_idx].children[RIGHT])
     }
    }

    spec fun is_bst(map: Map, cur_idx: u64): bool {
      (forall idx: u64 where vector::spec_contains(tset(map, map.nodes[cur_idx].children[LEFT]), idx): map.nodes[cur_idx].key > map.nodes[idx].key) &&
  (forall idx: u64 where vector::spec_contains(tset(map, map.nodes[cur_idx].children[RIGHT]), idx): map.nodes[cur_idx].key < map.nodes[idx].key) &&
is_bst(map, map.nodes[cur_idx].children[LEFT]) && is_bst(map, map.nodes[cur_idx].children[RIGHT])
    }


    public fun add(self: &mut Map, key: u32) {
        // Verify key does not already exist, push new node to back of nodes vector.
        let (node_index, parent_index, child_direction) = self.search(key);
        spec {
            // assert parent_index != NIL ==> parent_index < len(self.nodes);
        };
        assert!(node_index == NIL, E_KEY_ALREADY_EXISTS);
        spec {
            assert child_direction == LEFT || child_direction == RIGHT || child_direction == NIL;
        };
        node_index = self.nodes.length();
        // If tree is empty, set root to new node.
        if (parent_index == NIL) {
            self.root = node_index;
            self.nodes.push_back(
                Node {
                    key,
                    parent: parent_index,
                    children: vector[NIL, NIL]
                }
            );            
            return
        };

        self.nodes.push_back(
            Node {
                key,
                parent: parent_index,
                children: vector[NIL, NIL]
            }
        );


        // Set new node as child to parent on specified side.
        self.nodes[parent_index].children[child_direction] = node_index;
        spec {
            assert parent_index != NIL;
            assert parent_index < node_index;
            assert self.nodes[node_index].parent == parent_index;
            // assert forall idx: num where idx >= 0 && idx < node_index: 
            // self.nodes[idx].children[RIGHT] != NIL ==> self.nodes[self.nodes[idx].children[RIGHT]].parent == idx;              
            assert self.nodes[self.nodes[parent_index].children[child_direction]].parent == parent_index;
        };

    }
    spec add {
        // requires is_bst(self, self.root);
        invariant forall idx: num where idx >= 0 && idx < len(self.nodes):
            self.nodes[idx].children[LEFT] != NIL ==> idx < self.nodes[idx].children[LEFT];  
        invariant forall idx: num where idx >= 0 && idx < len(self.nodes):
            self.nodes[idx].children[RIGHT] != NIL ==> idx < self.nodes[idx].children[RIGHT];
        requires len(self.nodes) < NIL - 1;
        invariant forall idx_1: num, idx_2: num where idx_1 >= 0 && idx_1 < len(self.nodes) && idx_2 >= 0 && idx_2 < len(self.nodes) && idx_1 != idx_2: 
            self.nodes[idx_1].children[LEFT] != NIL ==> 
                         (self.nodes[idx_2].children[LEFT] != self.nodes[idx_1].children[LEFT]) &&  
                         (self.nodes[idx_2].children[RIGHT] != self.nodes[idx_1].children[LEFT]);
        invariant forall idx_1: num, idx_2: num where idx_1 >= 0 && idx_1 < len(self.nodes) && idx_2 >= 0 && idx_2 < len(self.nodes) && idx_1 != idx_2: 
            self.nodes[idx_1].children[RIGHT] != NIL ==> 
                         (self.nodes[idx_2].children[LEFT] != self.nodes[idx_1].children[RIGHT]) &&  
                         (self.nodes[idx_2].children[RIGHT] != self.nodes[idx_1].children[RIGHT]);           
        invariant self.root == NIL ==> len(self.nodes) == 0;
        ensures len(self.nodes) == len(old(self.nodes)) + 1;
        ensures self.nodes[len(self.nodes) - 1].key == key;
        invariant forall idx: num where idx >= 0 && idx < len(self.nodes): 
            self.nodes[idx].parent != NIL ==> (self.nodes[self.nodes[idx].parent].children[LEFT] == idx || self.nodes[self.nodes[idx].parent].children[RIGHT] == idx);                             
    }

    spec fun diff_subtree(nodes: vector<Node>, idx: u64): bool {
        if (nodes[idx].children[LEFT] != NIL || nodes[idx].children[RIGHT] != NIL) {
            nodes[idx].children[LEFT] != nodes[idx].children[RIGHT]
        } else {
            true
        }
    }

    spec fun search_spec_1(self: Map, key: u32, cur_idx: u64, step: u64, end: u64): u64 {
        if (cur_idx == NIL || step == end) {
            cur_idx
        } else {
            let s = spec_next_step(self, key, cur_idx);
            if (s == cur_idx) {
                cur_idx
            } else {
                search_spec_1(self, key, s, step + 1, end)
            }
        }
    }


    spec fun spec_next_step(self: &Map, key: u32, cur_idx: u64): u64 {
        if (cur_idx == NIL) {
            cur_idx
        } else {
            if (self.nodes[cur_idx].key == key) {
                cur_idx
            } else if (key < self.nodes[cur_idx].key ) {
                self.nodes[cur_idx].children[LEFT]
            } else {
                self.nodes[cur_idx].children[RIGHT]
            }            
        }
    }

    fun search_rec(self: &Map, key: u32, cur_idx: u64, step: u64, end: u64): (bool, u64) {
        if (cur_idx == NIL || step == end) {
            (false, cur_idx)
        } else {
            let (succ, s) = next_step(self, key, cur_idx);
            if (succ) {
                (succ, s)
            } else {
                search_rec(self, key, s, step + 1, end)
            }
        }
    }

    spec search_rec {
        pragma opaque;
        // invariant is_bst(self, self.root);
        ensures result_2 == search_spec_1(self, key, cur_idx, step, end);
    }  

    fun next_step(self: &Map, key: u32, cur_idx: u64): (bool, u64) {
        let current_node_ref;
        let current_key;
        if (cur_idx == NIL) {
            (false, cur_idx)
        } else {
            current_node_ref = &self.nodes[cur_idx];
            current_key = current_node_ref.key;
            if (current_key == key) {
                (true, cur_idx)
            } else if (key < current_key ) {
                (false, current_node_ref.children[LEFT])
            } else {
                (false, current_node_ref.children[RIGHT])
            }            
        }
    }

    spec next_step {
        // requires is_bst(self, cur_idx);
        ensures result_1 ==> cur_idx != NIL;
        // ensures result_1 ==> vector::spec_contains(tset(self, cur_idx), key);
        ensures result_1 ==> self.nodes[cur_idx].key == key;
        //ensures (!result_1 && result_2 == self.nodes[cur_idx].children[LEFT]) ==> !vector::spec_contains(tset(self, self.nodes[cur_idx].children[RIGHT]), key);
        ensures (cur_idx != NIL && self.nodes[cur_idx].key == key) ==> result_1;
        ensures cur_idx == NIL ==> !result_1;
        ensures (cur_idx != NIL && self.nodes[cur_idx].key != key) ==> !result_1;
        ensures result_2 == spec_next_step(self, key, cur_idx);
    }
 
    fun search(self: &Map, key: u32): (u64, u64, u64) {
        let current_index = self.root;
        let parent_index = NIL;
        let child_direction = NIL;
        let current_node_ref;
        let current_key;
        let index = 0;
        let traversed = vector[];
        while ({
            spec {
                invariant self.root == NIL ==> current_index == NIL;
                invariant self.root == NIL ==> parent_index == NIL;
                invariant self.root == NIL ==> child_direction == NIL;
                invariant (self.root != NIL && self.root != current_index) ==> parent_index != NIL;
                invariant (self.root != current_index && current_index != NIL) ==> parent_index != NIL;
                invariant child_direction == LEFT || child_direction == RIGHT || child_direction == NIL;
                invariant (self.root != NIL && current_index != self.root) ==> child_direction != NIL;
                invariant parent_index != NIL ==> parent_index < len(self.nodes);
                invariant forall idx: num where idx >= 0 && idx < len(self.nodes):
                    self.nodes[idx].children[LEFT] != NIL ==> idx < self.nodes[idx].children[LEFT];  
                invariant forall idx: num where idx >= 0 && idx < len(self.nodes):
                    self.nodes[idx].children[RIGHT] != NIL ==> idx < self.nodes[idx].children[RIGHT];   
                // invariant  current_index != NIL ==> current_index < NIL;          
                // invariant (self.root != NIL && index > 0) ==> current_index != self.root;
                // invariant parent_index != NIL ==> parent_index < current_index;
                invariant forall idx: num where idx >= 0 && idx < len(self.nodes):
                    diff_subtree(self.nodes, idx); 
                invariant child_direction != NIL ==>
                    self.nodes[parent_index].children[child_direction] == current_index;
                invariant current_index != NIL ==>
                    ((parent_index == NIL && child_direction == NIL) || (parent_index != NIL && child_direction != NIL));
                invariant
                    parent_index != NIL ==> 
                    current_index == search_spec_1(self, key, parent_index, index - 1, index);    
                invariant parent_index != NIL ==>
                     current_index ==  spec_next_step(self, key, parent_index);  
                invariant parent_index != NIL ==>  parent_index < current_index;
                invariant len(traversed) == index;
                invariant forall i: num  where i >= 0 && i < index: 
                    traversed[i] < current_index;
                invariant index == 0 <==> self.root == current_index;
                invariant index > 0 ==> traversed[0] == self.root;
                invariant forall idx: num where idx >= 0 && idx < len(self.nodes): 
            self.nodes[idx].parent != NIL ==> (self.nodes[self.nodes[idx].parent].children[LEFT] == idx || self.nodes[self.nodes[idx].parent].children[RIGHT] == idx);                          
            };
            current_index != NIL
            }) {
                traversed.push_back(current_index);
                current_node_ref = &self.nodes[current_index];
                current_key = current_node_ref.key;
                if (key == current_key) break;
                parent_index = current_index;
                child_direction = if (key < current_key) LEFT else RIGHT;
                current_index = current_node_ref.children[child_direction];
                spec {
                    assert parent_index < current_index;
                    assert traversed[index] < current_index;
                };
                index = index + 1;
        };
        spec {
            assert (index == 0 && self.root != NIL) ==> current_index == self.root;
            assert (index == 0 && self.root != NIL) ==> self.nodes[current_index].key == key;
            assert (self.root != NIL && current_index == self.root) ==> self.nodes[current_index].key == key;
            assert index == 0 <==> current_index == self.root;
            assert current_index != self.root ==> self.root < current_index;
            assert forall i: num  where i >= 0 && i < index: 
                traversed[i] < current_index;
        };
        (current_index, parent_index, child_direction)
    }

    spec search {
        //requires is_bst(self, self.root);
        invariant forall idx: num where idx >= 0 && idx < len(self.nodes):
            self.nodes[idx].children[LEFT] != NIL ==> idx < self.nodes[idx].children[LEFT];  
        invariant forall idx: num where idx >= 0 && idx < len(self.nodes):
            self.nodes[idx].children[RIGHT] != NIL ==> idx < self.nodes[idx].children[RIGHT];      
        invariant forall idx: num where idx >= 0 && idx < len(self.nodes):
            diff_subtree(self.nodes, idx); 
        invariant forall idx_1: num, idx_2: num where idx_1 >= 0 && idx_1 < len(self.nodes) && idx_2 >= 0 && idx_2 < len(self.nodes) && idx_1 != idx_2: 
            self.nodes[idx_1].children[LEFT] != NIL ==> 
                         ((self.nodes[idx_2].children[LEFT] != self.nodes[idx_1].children[LEFT]) &&  
                         (self.nodes[idx_2].children[RIGHT] != self.nodes[idx_1].children[LEFT]));
        invariant forall idx_1: num, idx_2: num where idx_1 >= 0 && idx_1 < len(self.nodes) && idx_2 >= 0 && idx_2 < len(self.nodes) && idx_1 != idx_2: 
            self.nodes[idx_1].children[RIGHT] != NIL ==> 
                         ((self.nodes[idx_2].children[LEFT] != self.nodes[idx_1].children[RIGHT]) &&  
                         (self.nodes[idx_2].children[RIGHT] != self.nodes[idx_1].children[RIGHT]));          
        invariant self.root == NIL ==> len(self.nodes) == 0;
        ensures self.root == NIL ==> result_1 == NIL;
        ensures self.root == NIL ==> result_2 == NIL;
        ensures self.root == NIL ==> result_3 == NIL;
        ensures result_1 != NIL ==> self.nodes[result_1].key == key;
        ensures (result_1 != NIL && result_3 == NIL) ==> result_1 == self.root;
        ensures result_1 != NIL ==> ((result_2 == NIL && result_3 == NIL) || (result_2 != NIL && result_3 != NIL));
        ensures (result_3 != NIL && result_1 != NIL) ==> self.nodes[result_2].children[result_3] == result_1;
        ensures (self.root != NIL && result_1 != self.root) ==> result_3 != NIL;
        ensures (self.root != NIL && result_1 != self.root) ==> result_2 != NIL;
        ensures result_2 != NIL ==> result_2 < len(self.nodes);
        ensures self.root != result_1 ==> self.root < result_1;
        ensures result_1 != NIL ==> (exists i: num where i >= 0 && i < len(self.nodes): self.nodes[i].key == key);
        invariant forall idx: num where idx >= 0 && idx < len(self.nodes): 
            self.nodes[idx].parent != NIL ==> (self.nodes[self.nodes[idx].parent].children[LEFT] == idx || self.nodes[self.nodes[idx].parent].children[RIGHT] == idx);               
    }




}
