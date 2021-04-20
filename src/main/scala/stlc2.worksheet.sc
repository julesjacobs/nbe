class prop
case class Base(x:String) extends prop {
  override def toString() = x
}
case class Arr(a:prop, b:prop) extends prop {
  override def toString() = s"($a -> $b)"
}

case class thm(prop:prop) {
  override def toString() = s"⊢ $prop"
}

def fail(msg:String) = assert(false, msg)

def app(a:thm, b:thm):thm =
  a.prop match {
    case Arr(c,d) => assert(b.prop == c, s"The proppes ${b.prop} and ${c} don't match."); thm(d)
    case _ => fail(s"Can't apply $a.")
  }

def lam(a:prop, f:thm => thm):thm = thm(Arr(a,f(thm(a)).prop))

val A = Base("A")
val B = Base("B")

val modusponens = lam(A, x => lam(Arr(A,B), f => app(f,x)))

case class And(a:prop, b:prop) extends prop {
  override def toString() = s"($a ∧ $b)"
}

def pair(a:thm, b:thm):thm = thm(And(a.prop,b.prop))

def fst(a:thm):thm =
  a.prop match {
    case And(a,b) => thm(a)
    case _ => fail(s"Can't do fst(${a.prop}).")
  }

def snd(a:thm) =
  a.prop match {
    case And(a,b) => thm(b)
    case _ => fail(s"Can't do snd(${a.prop}).")
  }

val flip = lam(And(A,B), x => pair(snd(x),fst(x)))

case class Or(a:prop, b:prop) extends prop {
  override def toString() = s"($a ∨ $b)"
}

def inl(a:thm, b:prop):thm = thm(Or(a.prop,b))
def inr(a:prop, b:thm):thm = thm(Or(a,b.prop))

def destr(a:thm, f:thm => thm, g:thm => thm):thm =
  a.prop match {
    case Or(a,b) =>
      val p = f(thm(a)); val q = g(thm(b));
      if(p == q) then p else fail(s"The proppes ${p.prop} and ${q.prop} are not equal.")
    case _ => fail(s"Can't do destr(${a.prop}).")
  }

val flop = lam(Or(A,B), x => destr(x, p => inr(B,p), q => inl(q,A)))