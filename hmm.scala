object foobar {

  type ProbaMatrix = Array [Array [Double]]
  val genericException = new IllegalArgumentException
  val epsilon = 1.0E-10

  def normalizeRow (x: Array[Double]) = {
    assume {x.forall (_ >= 0)}
    val s = x.sum
    assume (s > epsilon)
    x.map {_ / s}
  }

  def normalizeRows (x: ProbaMatrix) : ProbaMatrix = x.map {x => normalizeRow (x)}

  def toLog (x: Array[Double]) = 
    x.map {x => if (x > 0) Math.max (Math.log (x), Float.MinValue) else Float.MinValue}

  def toLog (x: ProbaMatrix) : ProbaMatrix = x.map {toLog (_)}

  def transpose (x: ProbaMatrix) = {
    val nrows = x.length
    val ncols = x (0).length
    val ret = Array.ofDim[Double](ncols, nrows)
    for (i <- 0 until nrows; j <- 0 until ncols) ret (j)(i) = x (i)(j)
    ret
  }

  val pTrans : ProbaMatrix = Array (Array (0.0, 0.5), Array (0.5, 0.5))
  val pEmit : ProbaMatrix = Array (Array (0.5, 0.5, 0.5), Array (0.5, 0.5, 0.5))

object HMMParameters {
  def apply (transProba: ProbaMatrix, emitProba: ProbaMatrix) = {
    val nbStates = transProba.length
    assume (nbStates > 1)
    assume (nbStates == emitProba.length)
    assume (transProba.forall {_.length == nbStates})

    val nbSymbols = {
      var (min, max) = emitProba.map (_.length).
        foldLeft ((Int.MaxValue, Int.MinValue)) {(x, y) => (Math.min (x._1, y), Math.max (x._2, y))}
 
      assume (max == min && max > 1)
      max
    }

    new HMMParameters (nbStates, nbSymbols, normalizeRows (transProba).transpose, normalizeRows (emitProba).transpose)
  }
}

class HMMParameters (val nbStates: Int, val nbSymbols: Int, val transProba: ProbaMatrix, val emitProba: ProbaMatrix) {
  val transLogP = toLog (transProba)
  val emitLogP = toLog (emitProba)
}

def viterbi (model: HMMParameters, observations: Array[Int], initStatesProbs: Array[Double]) = {
  assume (observations.length > 0)
  assume (observations.forall {x => x > 0 && x <= model.nbSymbols})
  assume (initStatesProbs.length == model.nbStates)

  val v = Array.ofDim[(Double, Int)] (observations.length, model.nbStates)
  toLog (normalizeRow (initStatesProbs)).
    zip (model.emitLogP (observations (0) - 1)).
    map {case (p, e) => (Math.max (p + e, Float.MinValue),0)}.
    copyToArray (v(0))

  for (i <- 1 until observations.length)
    model.transLogP.map {
      p => (p zip v (i - 1).map (_._1)).
        map {x => Math.max (x._1 + x._2, Float.MinValue)}.
        zipWithIndex.
        foldLeft ((Float.MinValue : Double, -1)) {case (a @ (max, _), b @ (x, _)) => if (x > max) b else a}
    }.zip (model.emitLogP (observations (i) - 1)).
      map {case ((v, i), e) => (Math.max (v + e, Float.MinValue), i)}.
      copyToArray (v (i))

  val (optimalLogP, lastSymbol) = 
    v (observations.length - 1).foldLeft ((Float.MinValue : Double, -1)) {case (a @ (max, _), b @ (x, _)) => if (x > max) b else a}

  val symbolsSeqOptimal = Array.ofDim[Int](observations.length)
  symbolsSeqOptimal (observations.length - 1) = lastSymbol
  for (i <- 0 to (observations.length - 2) by -1) symbolsSeqOptimal (i) = (v (i+1)(symbolsSeqOptimal (i+1)))._2

  (v, optimalLogP, symbolsSeqOptimal.map {_ + 1})
}


object test {
  val startProbs = Array[Double](1,1)
  val transProbs = Array[Array[Double]](Array (6, 4), Array (4, 6))
  val emitProbs =  Array[Array[Double]](Array (6, 4), Array (4, 6))
  val HMM = HMMParameters (transProbs, emitProbs)
  def apply () = {
    val observations : Array[Int] = Array (1, 1, 2, 2)
    viterbi (HMM, observations, startProbs)
  }
}

  def cumulatedDistribution (xs: Array[Double]) = {
    val ps = normalizeRow (xs).zipWithIndex.sortWith {_._1 >= _._1}

    for (i <- 1 until ps.length) ps (i) = (ps (i)._1 + ps (i - 1)._1, ps (i)._2)
    ps (ps.length - 1) = (1 : Double, ps (ps.length - 1)._2)
    ps
  }

  class GenParameter {
    var seed: Option[Long] = None
  }

  object GenMultinomial {
    def example = {
      var x = GenMultinomial (Array (1,2,3)).asStream.iterator
      x.take (100000).toVector.groupBy {x => x}.map {case (a,b) => (a, b.length)}
    }

    def apply (probs: Array[Double], param: GenParameter = new GenParameter) = 
      new GenMultinomial (probs, param)
  }

  class GenMultinomial (val probs: Array[Double], val param: GenParameter = new GenParameter) {
    val ps = cumulatedDistribution (probs)
    val g = scala.util.Random
    if (! param.seed.isEmpty) g.setSeed (param.seed.get)

    private def f = {
      val r = g.nextDouble
      ps.find {r <= _._1}.get._2 + 1
    }

    def apply (size: Int) = for (i <- 0 until size) yield f
    
    def asStream (): Stream[Int] = {
      def str: Stream [Int] = f #:: str
      str
    }
  }

  def genMultinomial (probs: Array[Double], param: GenParameter = new GenParameter)(size: Int) = {
    assume (size > 0)
    val ps = cumulatedDistribution (probs)
    
    val g = scala.util.Random
    if (! param.seed.isEmpty) g.setSeed (param.seed.get)

    for (i <- 0 until size) yield {
      val r = g.nextDouble
      ps.find {r <= _._1}.get._2 + 1
    }
  
  }

  def genDiscreteMarkov (transProbs: Array[Array[Double]], param: GenParameter = new GenParameter)(size: Int, start: Int) = {
    assume (size > 0)
    val ps = transProbs map cumulatedDistribution
    
    val g = scala.util.Random
    if (! param.seed.isEmpty) g.setSeed (param.seed.get)

    var stateNow = start
    for (i <- 0 until size) yield {
      val r = g.nextDouble
      stateNow = ps (stateNow).find {r <= _._1}.get._2
      stateNow
    }
  }

  def genDiscreteMarkovStream (transProbs: Array[Array[Double]], param: GenParameter = new GenParameter)(start: Int): Stream[Int] = {
    val ps = transProbs map cumulatedDistribution
    val g = scala.util.Random
    if (! param.seed.isEmpty) g.setSeed (param.seed.get)

    def f (s: Int) = {
      val r = g.nextDouble 
      ps (s).find {r <= _._1}.get._2
    }
    def str (s: Int): Stream[Int] = s #:: str (f (s)) 
    str (f (start))
  }

  // trés inefficace
  def genDiscreteMarkovFromStream (transProbs: Array[Array[Double]], size: Int, start: Int): Array[Int] = {
    genDiscreteMarkovStream (transProbs)(start).take (size).toArray
  }

  object GenDiscreteMarkov {
    def apply (transProbs: Array[Array[Double]], param: GenParameter = new GenParameter) = 
      new GenDiscreteMarkov (transProbs, param)
  }

  class GenDiscreteMarkov (val transProbs: Array[Array[Double]], val param: GenParameter = new GenParameter) {
    val ps = transProbs map cumulatedDistribution
    val g = scala.util.Random
    if (! param.seed.isEmpty) g.setSeed (param.seed.get)

    def f (s: Int) = {
      val r = g.nextDouble
      ps (s).find {r <= _._1}.get._2
    }

    def apply (size: Int, start: Int) = {
      var stateNow = start
      for (i <- 0 until size) yield stateNow = f (stateNow)
    }

    def asStream (start: Int) = {
      def str (s: Int): Stream[Int] = s #:: str (f (s))
      str (f (start))
    }
  }

  object GenMultinomialOnStates {
    def apply (emitProbs: Array[Array[Double]], param: GenParameter = new GenParameter) = 
      new GenMultinomialOnStates (emitProbs, param)
  }

  class GenMultinomialOnStates (val emitProbs: Array[Array[Double]], val param: GenParameter = new GenParameter) {
    val ps = emitProbs map cumulatedDistribution
    val g = scala.util.Random
    if (! param.seed.isEmpty) g.setSeed (param.seed.get)

    private def f (s: Int) = {
      val r = g.nextDouble
      ps (s).find {r <= _._1}.get._2 + 1
    }

    def apply (states: Array[Int]): Array[Int] = 
      for (state <- states) yield f (state - 1)

    def asStream (statesStream: Stream[Int]): Stream[(Int, Int)] = {
      val i = statesStream.iterator
      def str (s: Int): Stream[(Int, Int)] = (s, f(s)) #:: str (i.next)
      str (i.next)
    }
  }

  def genMultinomialOnStates (emitProbs: Array[Array[Double]], param: GenParameter = new GenParameter)(states: Array[Int]): Array[Int] = {
    val ps = emitProbs map cumulatedDistribution
    val g = scala.util.Random
    if (! param.seed.isEmpty) g.setSeed (param.seed.get)

    for (state <- states) yield {
      val r = g.nextDouble
      ps (state - 1).find {r <= _._1}.get._2 + 1
    }

  }

  def genMultinomialOnStateStream (emitProbs: Array[Array[Double]], param: GenParameter = new GenParameter)
    (statesStream: Stream[Int])
  : Stream[(Int, Int)] = {
    val ps = emitProbs map cumulatedDistribution
    val g = scala.util.Random
    if (! param.seed.isEmpty) g.setSeed (param.seed.get)
    
    def f (s: Int) = {
      val r = g.nextDouble
      ps (s).find {r <= _._1}.get._2 + 1
    }

    val i = statesStream.iterator
    def str (s: Int): Stream[(Int, Int)] = (s, f(s)) #:: str (i.next)
    str (i.next)
  }

  def eventStats (evts: Seq[(Int, Int)]) = {
    val facesPerState = evts.groupBy {case (a,b) => a}.
      map {case (state, events) => (state, events.map {case (_, face) => face})}
    facesPerState.map {case (state, faces) => (state, histogram (faces))}.
      toArray.sortBy {_._1}
  }

  object DishonnestCasino {
    val transProbs: Array[Array[Double]] = Array (Array (99, 1), Array (2, 98))
    val emitProbs: Array[Array[Double]] = Array (
      Array (1,1,1,1,1,1),
      Array (1,1,1,1,1,5))

    val hmm = HMMParameters (transProbs, emitProbs)
    val stateStream: Stream[Int] = GenDiscreteMarkov (transProbs).asStream (0)
    val eventStream: Stream[(Int, Int)] = genMultinomialOnStateStream (emitProbs)(stateStream)
    val eventIterator = eventStream.iterator
    def next: (Int, Int) = eventIterator.next
    def take (size: Int) = eventIterator.take (size)

    private def histogram (xs: Seq[Int]) = {
      xs.groupBy {x => x}.
        map {case (x, occurrences) => (x, occurrences.length)}.
        toArray.
        sorted
    }

    def stats  (size: Int) = eventStats (take (size).toArray)
  }

}
