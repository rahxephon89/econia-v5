
type setOfInt;

function emptySet() : setOfInt;
function singleton(x: int) : setOfInt;
function union(s1: setOfInt, s2: setOfInt) : setOfInt;
function in(x: int, s: setOfInt) : bool;

axiom (forall x: int :: !in(x, emptySet()));
axiom (forall x,y: int :: in(x, singleton(y)) <==> x == y);
axiom (forall x: int, s1, s2: setOfInt :: in(x, union(s1, s2)) <==> in(x, s1) || in(x, s2));
axiom (forall s1, s2: setOfInt :: union(s1, s2) == union(s2, s1));
axiom (forall s1: setOfInt :: union(s1, emptySet()) == s1);
axiom (forall s1, s2, s3: setOfInt :: union(union(s1, s2), s3) == union(s1, union(s2, s3)));



datatype Tree {
  Nil(),
  Node(left: Tree, value: int, right: Tree)
}


function treeElts(t: Tree) : setOfInt;


axiom (forall t: Tree ::
   treeElts(Nil()) == emptySet()
);

axiom (forall l: Tree, v: int, r: Tree ::
   treeElts(Node(l,v,r))
      == union(treeElts(l),
                    union(singleton(v), treeElts(r)))
);


function isBST(t: Tree) returns (b: bool);

axiom (forall t: Tree ::
  t == Nil()
  ==> isBST(t)
);

axiom (forall l: Tree, v: int, r: Tree ::
(isBST(Node(l,v,r))
       <==> ( isBST(l)
             && isBST(r)
             && (forall x: int :: in(x, treeElts(l)) ==> x < v)
             && (forall y: int :: in(y, treeElts(r)) ==> y > v)
           )
     )
);



function insert(t: Tree, x: int) : Tree {
    if t is Nil then
        Node(Nil(), x, Nil())
    else
        (
        var l, v, r := lOf(t), vOf(t), rOf(t);
        if x < v then
            Node(insert(l, x), v, r)
        else if x > v then
            Node(l, v, insert(r, x))
        else
            t
        )
}


function lOf(t: Tree) returns (res: Tree);
function vOf(t: Tree) returns (res: int);
function rOf(t: Tree) returns (res: Tree);


axiom (forall l: Tree, v: int, r: Tree ::
  lOf(Node(l,v,r)) == l
);
axiom (forall l: Tree, v: int, r: Tree ::
  vOf(Node(l,v,r)) == v
);
axiom (forall l: Tree, v: int, r: Tree ::
  rOf(Node(l,v,r)) == r
);



procedure proc_insert(t: Tree, x: int) returns (s: Tree)
  requires isBST(t);
  ensures s == insert(t, x);
  ensures isBST(s);
  ensures in(x, treeElts(s));
  ensures in(x, treeElts(t)) ==> s == t;
  ensures !in(x, treeElts(t)) ==> treeElts(s) == union(singleton(x), treeElts(t));
{
  var l: Tree;
  var v: int;
  var r: Tree;
  var l_t: Tree;
  var r_t: Tree;
  if (t is Nil) {
    s := insert(Nil(), x);
    assert isBST(s);
    assert in(x, treeElts(s));
    assert treeElts(s) == union(treeElts(Nil()), union(singleton(x), treeElts(Nil())));
    assert treeElts(s) == union(singleton(x), treeElts(t));
    return;
  } else {
    l := lOf(t);
    v := vOf(t);
    r := rOf(t);
    assert isBST(r);
    assert isBST(l);

    if (x < v) {
      call l_t := proc_insert(l, x);
      assert !in(x, treeElts(t)) ==> !in(x, treeElts(l));
      assert !in(x, treeElts(l)) ==> treeElts(l_t) == union(singleton(x), treeElts(l));

      assert in(x, treeElts(l_t));
      assert in(x, union(treeElts(l_t), union(singleton(v), treeElts(r))));
      s := Node(l_t, v, r);
      assert treeElts(Node(l_t, v, r)) == union(treeElts(l_t),union(singleton(v), treeElts(r)));
      assert !in(x, treeElts(l)) ==>
          treeElts(Node(l_t, v, r)) == union(union(singleton(x), treeElts(l)),union(singleton(v), treeElts(r)));
      assert !in(x, treeElts(l)) ==>
          treeElts(Node(l_t, v, r)) == union(singleton(x), union(treeElts(l), union(singleton(v), treeElts(r))));
      assert !in(x, treeElts(l)) ==>
          treeElts(Node(l_t, v, r)) == union(singleton(x), treeElts(t));
      assert !in(x, treeElts(s)) ==> treeElts(s) == union(singleton(x), treeElts(t));
      assert in(x, treeElts(Node(l_t, v, r)));
      return;
    } else if (x > v) {
      call r_t := proc_insert(r, x);
      assert !in(x, treeElts(t)) ==> !in(x, treeElts(r));
      assert !in(x, treeElts(r)) ==> treeElts(r_t) == union(singleton(x), treeElts(r));

      assert in(x, treeElts(r_t));
      assert in(x, union(singleton(v), treeElts(r_t)));
      assert in(x, union(treeElts(l), union(singleton(v), treeElts(r_t))));
      s := Node(l, v, r_t);
      assert treeElts(Node(l, v, r_t)) == union(treeElts(l),union(singleton(v), treeElts(r_t)));
      assert !in(x, treeElts(r)) ==> treeElts(Node(l, v, r_t)) == union(treeElts(l),union(singleton(v), union(singleton(x), treeElts(r))));
      assert !in(x, treeElts(r)) ==> treeElts(Node(l, v, r_t)) == union(treeElts(l),union(singleton(v), union(treeElts(r), singleton(x))));
      assert !in(x, treeElts(r)) ==> treeElts(Node(l, v, r_t)) == union(treeElts(l),union(union(singleton(v), treeElts(r)), singleton(x)));
      assert !in(x, treeElts(r)) ==> treeElts(Node(l, v, r_t)) == union(treeElts(l),union(union(singleton(v), treeElts(r)), singleton(x)));
      assert !in(x, treeElts(r)) ==> treeElts(Node(l, v, r_t)) == union(union(treeElts(l), union(singleton(v), treeElts(r))), singleton(x));
      assert !in(x, treeElts(r)) ==> treeElts(Node(l, v, r_t)) == union(treeElts(t), singleton(x));
      assert !in(x, treeElts(r)) ==> treeElts(Node(l, v, r_t)) == union(singleton(x), treeElts(t));
      assert !in(x, treeElts(s)) ==> treeElts(s) == union(singleton(x), treeElts(t));
      assert in(x, treeElts(Node(l, v, r_t)));
      return;
    } else {
       s := t;
       assert isBST(s);
       assert in(x, treeElts(s));
       return;
    }
  }
}

