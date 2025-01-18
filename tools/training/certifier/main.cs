// Dafny program main.dfy compiled into C#
// To recompile, you will need the libraries
//     System.Runtime.Numerics.dll System.Collections.Immutable.dll
// but the 'dotnet' tool in .NET should pick those up automatically.
// Optionally, you may want to include compiler switches like
//     /debug /nowarn:162,164,168,183,219,436,1717,1718

using System;
using System.Numerics;
using System.Collections;
[assembly: DafnyAssembly.DafnySourceAttribute(@"// dafny 4.9.2.0
// Command-line arguments: build --unicode-char false --target cs main.dfy IO/FileIO.cs
// main.dfy


module MainModule {
  method Main(args: seq<string>)
    decreases *
  {
    if |args| != 3 {
      print ""Usage: main <neural_network_input.txt> <GRAM_ITERATIONS>\n"";
      print ""Usage: main <neural_network_input.txt> <lipshitz_bounds_input.txt>\n"";
      return;
    }
    var neuralNetStr: string := ReadFromFile(args[1]);
    var maybeNeuralNet: (bool, NeuralNetwork) := ParseNeuralNet(neuralNetStr);
    expect maybeNeuralNet.0, ""Failed to parse neural network."";
    var neuralNet: NeuralNetwork := maybeNeuralNet.1;
    var lipBounds: seq<seq<real>>;
    print ""[\n"";
    if StringUtils.IsInt(args[2]) {
      var GRAM_ITERATIONS: int := StringUtils.ParseInt(args[2]);
      if GRAM_ITERATIONS <= 0 {
        print ""<GRAM_ITERATIONS> should be positive"";
        return;
      }
      var L := new LipschitzBounds(GRAM_ITERATIONS);
      var specNorms: seq<real> := GenerateSpecNorms(L, neuralNet);
      lipBounds := GenMarginLipBounds(L, neuralNet, specNorms);
      print ""{\n"";
      print ""  \""lipschitz_bounds\"": "", lipBounds, "",\n"";
      print ""  \""GRAM_ITERATIONS\"": "", GRAM_ITERATIONS, "",\n"";
      print ""  \""provenance\"": \""generated\""\n"";
      print ""}\n"";
    } else {
      print ""Reading margin lipschitz bounds from a file not (currently) supported\n"";
      return;
    }
    var inputStr: string := ReadFromFile(""/dev/stdin"");
    var lines: seq<string> := StringUtils.Split(inputStr, '\n');
    if |lines| <= 0 {
      return;
    }
    var l := 0;
    while l < |lines|
      decreases |lines| - l
    {
      var line := lines[l];
      l := l + 1;
      var inputSeq: seq<string> := StringUtils.Split(line, ' ');
      if |inputSeq| != 2 {
        print ""]\n"";
        return;
      }
      if inputSeq[0] == """" {
        print ""]\n"";
        return;
      }
      var realsStr: seq<string> := StringUtils.Split(inputSeq[0], ',');
      var areReals: bool := AreReals(realsStr);
      if !areReals {
        print ""Error: The given output vector contained non-real values.\n"";
        continue;
      }
      var outputVector := ParseReals(realsStr);
      if inputSeq[1] == """" {
        print ""Error: The given error margin was found to be empty.\n"";
        continue;
      }
      var isReal: bool := StringUtils.IsReal(inputSeq[1]);
      if !isReal {
        print ""Error: The given error margin is not of type real.\n"";
        continue;
      }
      var errorMargin := StringUtils.ParseReal(inputSeq[1]);
      if |outputVector| != |lipBounds| {
        print ""Error: Expected a vector of size "", |lipBounds|, "", but got "", |outputVector|, "".\n"";
        continue;
      }
      var robust: bool := Certify(outputVector, errorMargin, lipBounds);
      assert robust ==> forall v: Vector {:trigger Robust(v, outputVector, errorMargin, neuralNet)} {:trigger NN(neuralNet, v)} {:trigger CompatibleInput(v, neuralNet)} | CompatibleInput(v, neuralNet) && NN(neuralNet, v) == outputVector :: Robust(v, outputVector, errorMargin, neuralNet);
      print "",\n"";
      print ""{\n"";
      print ""\""output\"": "";
      print outputVector, "",\n"";
      print ""\""radius\"": "";
      print errorMargin, "",\n"";
      print ""\""certified\"": "";
      print robust, ""\n"";
      print ""}\n"";
    }
    print ""]\n"";
  }

  method ParseNeuralNet(xs: string) returns (t: (bool, NeuralNetwork))
    decreases xs
  {
    var err: string := """";
    var matrices: seq<Matrix> := [];
    var i := 0;
    while i < |xs|
      decreases |xs| - i
    {
      if i >= |xs| - 1 || xs[i .. i + 2] != ""[["" {
        print ""One"";
        return (false, [[[0.0]]]);
      }
      var j := i + 2;
      while xs[j - 2 .. j] != ""]]""
        invariant j <= |xs|
        decreases |xs| - j
      {
        if j >= |xs| {
          print ""Two"";
          return (false, [[[0.0]]]);
        }
        j := j + 1;
      }
      var ys := xs[i + 1 .. j - 1];
      var k := 0;
      var vectors: seq<Vector> := [];
      while k < |ys|
        decreases |ys| - k
      {
        if ys[k] != '[' {
          print ""Three"";
          return (false, [[[0.0]]]);
        }
        var l := k;
        while ys[l] != ']'
          invariant l < |ys|
          decreases |ys| - l
        {
          if l + 1 >= |ys| {
            print ""Four"";
            return (false, [[[0.0]]]);
          }
          l := l + 1;
        }
        var zs := ys[k + 1 .. l];
        var realsStr: seq<string> := StringUtils.Split(zs, ',');
        var areReals: bool := AreReals(realsStr);
        if !areReals {
          print ""Five\n"";
          return (false, [[[0.0]]]);
        }
        var v: seq<real> := ParseReals(realsStr);
        if |v| == 0 {
          return (false, [[[0.0]]]);
        }
        var v': Vector := v;
        vectors := vectors + [v'];
        k := l + 2;
      }
      var matrixWellFormed := IsMatrixWellFormed(vectors);
      if !matrixWellFormed {
        print ""Six"";
        return (false, [[[0.0]]]);
      }
      var matrix: Matrix := vectors;
      matrices := matrices + [Transpose(matrix)];
      i := j + 1;
    }
    var neuralNetWellFormed := IsNeuralNetWellFormed(matrices);
    if !neuralNetWellFormed {
      print ""Seven\n"";
      print |matrices|, ""\n"";
      if |matrices| == 2 {
        print |matrices[0]|, ""\n"";
        if |matrices[0]| > 0 {
          print |matrices[0][0]|, ""\n"";
        }
        print |matrices[1]|, ""\n"";
        if |matrices[1]| > 0 {
          print |matrices[1][0]|, ""\n"";
        }
      }
      return (false, [[[0.0]]]);
    }
    var neuralNet: NeuralNetwork := matrices;
    return (true, neuralNet);
  }

  method IsNeuralNetWellFormed(n: seq<Matrix>) returns (b: bool)
    ensures b ==> |n| > 0 && forall i: int, _t#0: int {:trigger n[_t#0], n[i]} | _t#0 == i + 1 :: 0 <= i && i < |n| - 1 ==> |n[i]| == |n[_t#0][0]|
    decreases n
  {
    if |n| == 0 {
      return false;
    }
    var i := 0;
    while i < |n| - 1
      invariant 0 <= i <= |n| - 1
      invariant forall j: int, _t#0: int {:trigger n[_t#0], n[j]} | _t#0 == j + 1 && 0 <= j && j < i :: |n[j]| == |n[_t#0][0]|
      decreases |n| - 1 - i
    {
      if |n[i]| != |n[i + 1][0]| {
        return false;
      }
      i := i + 1;
    }
    return true;
  }

  method IsMatrixWellFormed(m: seq<seq<real>>) returns (b: bool)
    ensures b ==> |m| > 0 && |m[0]| > 0 && forall i: int, j: int {:trigger m[j], m[i]} :: 0 <= i < |m| && 0 <= j < |m| ==> |m[i]| == |m[j]|
    decreases m
  {
    if |m| == 0 || |m[0]| == 0 {
      return false;
    }
    var size := |m[0]|;
    var i := 1;
    while i < |m|
      invariant 0 <= i <= |m|
      invariant forall j: int {:trigger m[j]} | 0 <= j < i :: |m[j]| == size
      decreases |m| - i
    {
      if |m[i]| != size {
        return false;
      }
      i := i + 1;
    }
    return true;
  }

  method AreReals(realsStr: seq<string>) returns (b: bool)
    ensures b ==> forall i: int {:trigger realsStr[i]} | 0 <= i < |realsStr| :: _default.IsReal(realsStr[i])
    decreases realsStr
  {
    for i: int := 0 to |realsStr|
      invariant forall j: int {:trigger realsStr[j]} | 0 <= j < i :: _default.IsReal(realsStr[j])
    {
      var isReal := StringUtils.IsReal(realsStr[i]);
      if !isReal {
        print realsStr[i];
        print ""\n"";
        return false;
      }
    }
    return true;
  }

  method ParseReals(realsStr: seq<string>) returns (reals: seq<real>)
    requires forall i: int {:trigger realsStr[i]} | 0 <= i < |realsStr| :: _default.IsReal(realsStr[i])
    decreases realsStr
  {
    reals := [];
    for i: int := 0 to |realsStr| {
      var r := StringUtils.ParseReal(realsStr[i]);
      reals := reals + [r];
    }
  }

  method ReadFromFile(filename: string) returns (str: string)
    decreases filename
  {
    var readResult := FileIO.ReadBytesFromFile(filename);
    expect readResult.Success?, ""Unexpected failure reading from "" + filename + "": "" + readResult.error;
    str := seq(|readResult.value|, (i: int) requires 0 <= i < |readResult.value| => readResult.value[i] as char);
  }

  import FileIO

  import StringUtils

  import opened Lipschitz

  import BasicArithmetic
}

module BasicArithmetic {
  const ROUNDING_PRECISION := 16
  const SQRT_ITERATIONS := 5000
  const SQRT_ERR_MARGIN := 0.0000001
  const DEBUG := true

  opaque ghost function Relu(x: real): (r: real)
    ensures x >= 0.0 ==> r == x
    ensures x < 0.0 ==> r == 0.0
    decreases x
  {
    if x >= 0.0 then
      x
    else
      0.0
  }

  opaque ghost function Sqrt(x: real): (r: real)
    requires x >= 0.0
    ensures {:axiom} r >= 0.0
    ensures {:axiom} r * r == x
    decreases x

  ghost function Power2Root(x: real, i: nat): (r: real)
    requires x >= 0.0
    decreases x, i
  {
    if i == 0 then
      x
    else
      Sqrt(Power2Root(x, i - 1))
  }

  function Abs(x: real): real
    decreases x
  {
    if x >= 0.0 then
      x
    else
      -x
  }

  ghost function Pow(x: real, y: nat): real
    decreases x, y
  {
    if y == 0 then
      1.0
    else
      x * Pow(x, y - 1)
  }

  function Square(x: real): (r: real)
    ensures r >= 0.0
    decreases x
  {
    x * x
  }

  method Power2RootUpperBound(x: real, i: nat) returns (r: real)
    requires x >= 0.0
    ensures r >= Power2Root(x, i)
    decreases x, i
  {
    var j := i;
    r := x;
    while j > 0
      invariant 0 <= j <= i
      invariant r >= Power2Root(x, i - j)
      decreases j - 0
    {
      MonotonicSqrt(Power2Root(x, i - j), r);
      r := SqrtUpperBound(r);
      j := j - 1;
    }
  }

  method SqrtUpperBound(x: real) returns (r: real)
    requires x >= 0.0
    ensures r >= Sqrt(x)
    decreases x
  {
    if x == 0.0 {
      SqrtZeroIsZero();
      return 0.0;
    }
    r := if x < 1.0 then 1.0 else x;
    var i := 0;
    while i < SQRT_ITERATIONS
      invariant r >= Sqrt(x) > 0.0
      decreases SQRT_ITERATIONS - i
    {
      var old_r := r;
      assert Sqrt(x) <= (r + x / r) / 2.0 by {
        assert 0.0 <= (r - Sqrt(x)) * (r - Sqrt(x));
        assert 0.0 <= r * r - 2.0 * r * Sqrt(x) + x;
        assert 0.0 <= (r * r - 2.0 * r * Sqrt(x) + x) / r;
        assert 0.0 <= r - 2.0 * Sqrt(x) + x / r;
        assert 2.0 * Sqrt(x) <= r + x / r;
        assert Sqrt(x) <= (r + x / r) / 2.0;
      }
      r := RoundUp((r + x / r) / 2.0);
      i := i + 1;
      if old_r - r < SQRT_ERR_MARGIN {
        return;
      }
    }
    print ""WARNING: Sqrt algorithm terminated early after reaching "", SQRT_ITERATIONS, "" iterations.\n"";
  }

  method RoundUp(x: real) returns (r: real)
    requires x >= 0.0
    ensures r >= x
    decreases x
  {
    var i := 0;
    r := x;
    while r != r.Floor as real && i < ROUNDING_PRECISION
      invariant r == x * Pow(10.0, i)
      decreases ROUNDING_PRECISION - i
    {
      r := r * 10.0;
      i := i + 1;
    }
    if r != r.Floor as real {
      r := r + 1.0;
    }
    r := r.Floor as real;
    while i > 0
      invariant r >= x * Pow(10.0, i)
      decreases i - 0
    {
      r := r / 10.0;
      i := i - 1;
    }
  }

  method PrintReal(x: real, n: nat)
    decreases x, n
  {
    var z: int := x.Floor;
    print z;
    print '.';
    var y: real := x;
    var i: nat := 0;
    while i < n
      decreases n - i
    {
      y := y * 10.0;
      z := z * 10;
      i := i + 1;
    }
    print y.Floor - z;
  }

  lemma /*{:_inductionTrigger Power2Root(Sqrt(x), i)}*/ /*{:_induction x, i}*/ Power2RootDef(x: real, i: nat)
    requires x >= 0.0
    ensures Power2Root(x, i + 1) == Power2Root(Sqrt(x), i)
    decreases x, i
  {
  }

  lemma /*{:_inductionTrigger Power2Root(y, i), Power2Root(x, i)}*/ /*{:_induction x, y, i}*/ Power2RootMonotonic(x: real, y: real, i: nat)
    requires 0.0 <= x <= y
    ensures Power2Root(x, i) <= Power2Root(y, i)
    decreases x, y, i
  {
    if i != 0 {
      Power2RootMonotonic(x, y, i - 1);
      MonotonicSqrt(Power2Root(x, i - 1), Power2Root(y, i - 1));
    }
  }

  lemma SqrtOfSquare()
    ensures forall x: real {:trigger Abs(x)} {:trigger Square(x)} :: Sqrt(Square(x)) == Abs(x)
  {
    assert forall x: real {:trigger Abs(x)} {:trigger Square(x)} :: Sqrt(Square(x)) * Sqrt(Square(x)) == Abs(x) * Abs(x);
    forall x: real | true {
      PositiveSquaresEquality(Sqrt(Square(x)), Abs(x));
    }
  }

  lemma PositiveSquaresEquality(x: real, y: real)
    requires x >= 0.0 && y >= 0.0
    requires x * x == y * y
    ensures x == y
    decreases x, y
  {
    if x > y {
      IncreaseSquare(x, y);
    } else if x < y {
      IncreaseSquare(y, x);
    }
  }

  lemma SqrtZeroIsZero()
    ensures Sqrt(0.0) == 0.0
  {
    if Sqrt(0.0) != 0.0 {
      calc {
        0.0;
      <
        Sqrt(0.0) * Sqrt(0.0);
      ==
        0.0;
      }
    }
  }

  lemma MonotonicSqrt(x: real, y: real)
    requires 0.0 <= x <= y
    ensures Sqrt(x) <= Sqrt(y)
    decreases x, y
  {
    if Sqrt(x) > Sqrt(y) {
      IncreaseSquare(Sqrt(x), Sqrt(y));
      assert false;
    }
  }

  lemma Increase(x: real, y: real, z: real)
    requires z > 0.0
    requires x > y
    ensures x * z > y * z
    decreases x, y, z
  {
  }

  lemma IncreaseSquare(x: real, y: real)
    requires 0.0 <= y < x
    ensures y * y < x * x
    decreases x, y
  {
    if y == 0.0 {
      Increase(x, 0.0, x);
    } else {
      Increase(x, y, x);
      Increase(x, y, y);
    }
  }

  lemma MonotonicSquarePositive(x: real, y: real)
    requires 0.0 <= x <= y
    ensures Square(x) <= Square(y)
    decreases x, y
  {
    assert 0.0 <= y;
  }

  lemma AbsoluteSquare(x: real)
    ensures Square(Abs(x)) == Square(x)
    decreases x
  {
  }

  lemma MonotonicSquare(x: real, y: real)
    requires Abs(x) <= Abs(y)
    ensures Square(x) <= Square(y)
    decreases x, y
  {
    MonotonicSquarePositive(Abs(x), Abs(y));
    AbsoluteSquare(x);
    AbsoluteSquare(y);
  }
}

module Lipschitz {
  function NonEmptyVector(): Vector
  {
    [0.0]
  }

  function NonEmptyMatrix(): Matrix
  {
    [[0.0]]
  }

  opaque function Product(s: seq<real>): (r: real)
    decreases s
  {
    if |s| == 0 then
      1.0
    else
      Product(s[..|s| - 1]) * s[|s| - 1]
  }

  lemma /*{:_inductionTrigger Product(s)}*/ /*{:_inductionTrigger |s|}*/ /*{:_induction s}*/ PositiveProduct(s: seq<real>)
    requires forall i: int {:trigger s[i]} | 0 <= i < |s| :: 0.0 <= s[i]
    ensures 0.0 <= Product(s)
    decreases s
  {
    reveal Product();
  }

  lemma /*{:_inductionTrigger Product(s0), Product(s)}*/ /*{:_inductionTrigger Product(s0), |s|}*/ /*{:_induction s, s0}*/ ProductDef(s: seq<real>, s0: seq<real>, s': real)
    requires |s| > 0
    requires s0 == s[..|s| - 1]
    requires s' == s[|s| - 1]
    ensures Product(s) == s' * Product(s0)
    decreases s, s0, s'
  {
    reveal Product();
  }

  opaque function Sum(s: seq<real>): (r: real)
    ensures (forall i: int {:trigger s[i]} | 0 <= i < |s| :: 0.0 <= s[i]) ==> r >= 0.0
    decreases s
  {
    if |s| == 0 then
      0.0
    else
      Sum(s[..|s| - 1]) + s[|s| - 1]
  }

  lemma /*{:_inductionTrigger Sum(s2), Sum(s1)}*/ /*{:_inductionTrigger Sum(s2), |s1|}*/ /*{:_inductionTrigger Sum(s1), |s2|}*/ /*{:_inductionTrigger |s2|, |s1|}*/ /*{:_induction s1, s2}*/ MonotonicSum(s1: seq<real>, s2: seq<real>)
    requires |s1| == |s2|
    requires forall i: int {:trigger s2[i]} {:trigger s1[i]} | 0 <= i < |s1| :: s1[i] <= s2[i]
    ensures Sum(s1) <= Sum(s2)
    decreases s1, s2
  {
    reveal Sum();
  }

  function Minus(v: Vector, u: Vector): (r: Vector)
    requires |v| == |u|
    ensures |r| == |v|
    ensures forall i: int {:trigger u[i]} {:trigger v[i]} {:trigger r[i]} :: 0 <= i < |r| ==> r[i] == v[i] - u[i]
    decreases v, u
  {
    if |v| == 1 then
      [v[0] - u[0]]
    else
      [v[0] - u[0]] + Minus(v[1..], u[1..])
  }

  opaque ghost function L2(v: Vector): (r: real)
    decreases v
  {
    Sqrt(Sum(Apply(v, Square)))
  }

  lemma NormOfOneDimensionIsAbs()
    ensures forall v: Vector {:trigger v[0]} {:trigger L2(v)} {:trigger |v|} | |v| == 1 :: L2(v) == Abs(v[0])
  {
    reveal L2();
    reveal Sum();
    assert forall v: Vector {:trigger v[0]} {:trigger Apply(v, Square)} {:trigger |v|} | |v| == 1 :: Sum(Apply(v, Square)) == v[0] * v[0];
    SqrtOfSquare();
  }

  lemma MonotonicL2(v: Vector, u: Vector)
    requires |v| == |u|
    requires forall i: int {:trigger u[i]} {:trigger v[i]} | 0 <= i < |v| :: Abs(v[i]) <= Abs(u[i])
    ensures L2(v) <= L2(u)
    decreases v, u
  {
    reveal L2();
    for i: int := 0 to |v|
      invariant forall j: int {:trigger u[j]} {:trigger v[j]} | 0 <= j < i :: Square(v[j]) <= Square(u[j])
    {
      MonotonicSquare(v[i], u[i]);
    }
    MonotonicSum(Apply(v, Square), Apply(u, Square));
    MonotonicSqrt(Sum(Apply(v, Square)), Sum(Apply(u, Square)));
  }

  ghost function Distance(v: Vector, u: Vector): real
    requires |v| == |u|
    decreases v, u
  {
    L2(Minus(v, u))
  }

  opaque function Apply(v: Vector, f: real -> real): (r: Vector)
    ensures |v| == |r|
    ensures forall i: int {:trigger v[i]} {:trigger r[i]} :: 0 <= i < |r| ==> r[i] == f(v[i])
    decreases v
  {
    if |v| == 1 then
      [f(v[0])]
    else
      [f(v[0])] + Apply(v[1..], f)
  }

  opaque function Dot(v: Vector, u: Vector): real
    requires |v| == |u|
    decreases v, u
  {
    if |v| == 1 then
      v[0] * u[0]
    else
      v[0] * u[0] + Dot(v[1..], u[1..])
  }

  opaque function MV(m: Matrix, v: Vector): (r: Vector)
    requires |m[0]| == |v|
    ensures |r| == |m|
    ensures forall i: int {:trigger m[i]} {:trigger r[i]} :: 0 <= i < |r| ==> r[i] == Dot(m[i], v)
    decreases m, v
  {
    if |m| == 1 then
      [Dot(m[0], v)]
    else
      [Dot(m[0], v)] + MV(m[1..], v)
  }

  opaque ghost function ApplyRelu(v: Vector): (r: Vector)
    ensures |r| == |v|
    ensures forall i: int {:trigger v[i]} {:trigger r[i]} :: 0 <= i < |r| ==> r[i] == Relu(v[i])
    ensures forall i: int {:trigger v[i]} {:trigger r[i]} :: 0 <= i < |r| ==> Abs(r[i]) <= Abs(v[i])
    decreases v
  {
    Apply(v, Relu)
  }

  method GenerateSpecNorms(L: LipschitzBounds, n: NeuralNetwork) returns (r: seq<real>)
    ensures |r| == |n|
    ensures forall i: int {:trigger n[i]} {:trigger r[i]} | 0 <= i < |n| :: IsSpecNormUpperBound(r[i], n[i])
    decreases L, n
  {
    var i := 0;
    r := [];
    while i < |n|
      invariant 0 <= i == |r| <= |n|
      invariant forall j: int {:trigger n[j]} {:trigger r[j]} | 0 <= j < i :: IsSpecNormUpperBound(r[j], n[j])
      decreases |n| - i
    {
      if DEBUG {
        print ""{ \""debug_msg\"": \""Generating spectral norm "", i, "" of "", |n|, ""...\"" },\n"";
      }
      var specNorm := L.GramIterationSimple(n[i]);
      assert specNorm >= SpecNorm(n[i]);
      r := r + [specNorm];
      i := i + 1;
    }
  }

  function SumPositiveMatrix(m: Matrix): (r: real)
    requires forall i: int, j: int {:trigger m[i][j]} | 0 <= i < |m| && 0 <= j < |m[0]| :: 0.0 <= m[i][j]
    ensures 0.0 <= r
    decreases m
  {
    if |m| == 1 then
      SumPositive(m[0])
    else
      SumPositive(m[0]) + SumPositiveMatrix(m[1..])
  }

  function SumPositive(v: Vector): (r: real)
    requires forall i: int {:trigger v[i]} | 0 <= i < |v| :: 0.0 <= v[i]
    ensures 0.0 <= r
    decreases v
  {
    if |v| == 1 then
      v[0]
    else
      v[0] + SumPositive(v[1..])
  }

  function SquareMatrixElements(m: Matrix): (r: Matrix)
    ensures forall i: int, j: int {:trigger r[i][j]} | 0 <= i < |r| && 0 <= j < |r[0]| :: 0.0 <= r[i][j]
    decreases m
  {
    if |m| == 1 then
      [Apply(m[0], Square)]
    else
      [Apply(m[0], Square)] + SquareMatrixElements(m[1..])
  }

  ghost function FrobeniusNorm(m: Matrix): real
    decreases m
  {
    Sqrt(SumPositiveMatrix(SquareMatrixElements(m)))
  }

  method FrobeniusNormUpperBound(m: Matrix) returns (r: real)
    ensures r >= FrobeniusNorm(m)
    decreases m
  {
    if DEBUG {
      print ""{ \""debug_msg\"": \""Computing frobenius norm upper bound for matrix of size "", |m|, ""x"", |m[0]|, ""\"" },\n"";
    }
    r := SqrtUpperBound(SumPositiveMatrix(SquareMatrixElements(m)));
  }

  method L2UpperBound(v: Vector) returns (r: real)
    ensures r >= L2(v)
    decreases v
  {
    if DEBUG {
      print ""{ \""debug_msg\"": \""Computing L2 norm for vector of length "", |v|, ""\"" },\n"";
    }
    r := SqrtUpperBound(Sum(Apply(v, Square)));
  }

  function GetFirstColumn(m: Matrix): (r: Vector)
    ensures |r| == |m|
    decreases m
  {
    if |m| == 1 then
      [m[0][0]]
    else
      [m[0][0]] + GetFirstColumn(m[1..])
  }

  function RemoveFirstColumn(m: Matrix): (r: Matrix)
    requires |m[0]| > 1
    ensures |r| == |m|
    decreases m
  {
    if |m| == 1 then
      [m[0][1..]]
    else
      [m[0][1..]] + RemoveFirstColumn(m[1..])
  }

  function Transpose(m: Matrix): (r: Matrix)
    decreases |m[0]|
  {
    if |m[0]| == 1 then
      [GetFirstColumn(m)]
    else
      [GetFirstColumn(m)] + Transpose(RemoveFirstColumn(m))
  }

  function MM(m: Matrix, n: Matrix): Matrix
    requires |m[0]| == |n|
    decreases m, n
  {
    if |m| == 1 then
      [MMGetRow(m[0], n)]
    else
      [MMGetRow(m[0], n)] + MM(m[1..], n)
  }

  function MMGetRow(v: Vector, n: Matrix): (r: Vector)
    requires |v| == |n|
    ensures |r| == |n[0]|
    decreases |n[0]|
  {
    if |n[0]| == 1 then
      [Dot(v, GetFirstColumn(n))]
    else
      [Dot(v, GetFirstColumn(n))] + MMGetRow(v, RemoveFirstColumn(n))
  }

  lemma {:axiom} Assumption1(m: Matrix)
    ensures SpecNorm(m) <= Sqrt(SpecNorm(MM(Transpose(m), m)))
    decreases m

  lemma {:axiom} Assumption2(m: Matrix)
    ensures SpecNorm(m) <= FrobeniusNorm(m)
    decreases m

  ghost function {:axiom} SpecNorm(m: Matrix): (r: real)
    ensures r >= 0.0
    ensures IsSpecNormUpperBound(r, m)
    ensures !exists x: real {:trigger IsSpecNormUpperBound(x, m)} :: 0.0 <= x < r && IsSpecNormUpperBound(x, m)
    decreases m

  lemma SpecNormUpperBoundProperty(s: real, m: Matrix)
    requires s >= SpecNorm(m)
    ensures s >= 0.0
    ensures IsSpecNormUpperBound(s, m)
    decreases s, m
  {
    PositiveL2();
  }

  lemma PositiveL2()
    ensures forall v: Vector {:trigger L2(v)} :: L2(v) >= 0.0
  {
    reveal L2();
  }

  ghost predicate IsSpecNormUpperBound(s: real, m: Matrix)
    decreases s, m
  {
    s >= 0.0 &&
    forall v: Vector {:trigger MV(m, v)} {:trigger |v|} | |v| == |m[0]| :: 
      L2(MV(m, v)) <= s * L2(v)
  }

  opaque ghost function NN(n: NeuralNetwork, v: Vector): (r: Vector)
    requires CompatibleInput(v, n)
    ensures CompatibleOutput(r, n)
    ensures |n| == 1 ==> r == ApplyRelu(MV(n[0], v))
    decreases n, v
  {
    if |n| == 1 then
      Layer(n[0], v)
    else
      Layer(n[|n| - 1], NN(n[..|n| - 1], v))
  }

  ghost function Layer(m: Matrix, v: Vector): (r: Vector)
    requires |v| == |m[0]|
    decreases m, v
  {
    ApplyRelu(MV(m, v))
  }

  ghost predicate CompatibleInput(v: Vector, n: NeuralNetwork)
    decreases v, n
  {
    |v| == |n[0][0]|
  }

  ghost predicate CompatibleOutput(v: Vector, n: NeuralNetwork)
    decreases v, n
  {
    |v| == |n[|n| - 1]|
  }

  method Certify(v': Vector, e: real, L: seq<seq<real>>)
      returns (b: bool)
    requires forall i: int, k: int {:trigger L[i][k]} | 0 <= i < |L| && 0 <= k < |L| :: 0.0 <= L[i][k]
    requires |v'| == |L|
    ensures b ==> forall v: Vector, n: NeuralNetwork {:trigger Robust(v, v', e, n)} {:trigger NN(n, v)} {:trigger CompatibleInput(v, n)} | CompatibleInput(v, n) && NN(n, v) == v' && AreMarginLipBounds(n, L) :: Robust(v, v', e, n)
    decreases v', e, L
  {
    var x := ArgMax(v');
    var i := 0;
    b := true;
    while i < |v'|
      invariant 0 <= i <= |v'|
      decreases |v'| - i
    {
      if i != x {
        if Abs(v'[x] - v'[i]) <= e * L[i][x] {
          b := false;
          break;
        }
      }
      i := i + 1;
    }
    if b {
    }
  }

  lemma ProveRobust(v': Vector, e: real, L: seq<real>, x: int)
    requires forall i: int {:trigger L[i]} | 0 <= i < |L| :: 0.0 <= L[i]
    requires |v'| == |L|
    requires x == ArgMax(v')
    requires forall i: int {:trigger L[i]} {:trigger v'[i]} | 0 <= i < |v'| && i != x :: v'[x] - L[x] * e > v'[i] + L[i] * e
    ensures forall v: Vector, n: NeuralNetwork {:trigger Robust(v, v', e, n)} {:trigger NN(n, v)} {:trigger CompatibleInput(v, n)} | CompatibleInput(v, n) && NN(n, v) == v' && AreLipBounds(n, L) :: Robust(v, v', e, n)
    decreases v', e, L, x
  {
    ProveRobustHelper(v', e, L, x);
    assert forall n: NeuralNetwork, v: Vector, u: Vector {:trigger NN(n, u), NN(n, v)} {:trigger NN(n, v), Distance(v, u)} {:trigger Distance(v, u), CompatibleInput(v, n)} {:trigger Distance(v, u), AreLipBounds(n, L)} | |n[|n| - 1]| == |L| && AreLipBounds(n, L) && |v| == |u| && CompatibleInput(v, n) && Distance(v, u) <= e && v' == NN(n, v) :: NN(n, u)[x] >= v'[x] - L[x] * e && forall i: int {:trigger L[i]} {:trigger v'[i]} {:trigger NN(n, u)[i]} | 0 <= i < |L| && i != x :: NN(n, u)[i] <= v'[i] + L[i] * e;
    assert forall n: NeuralNetwork, v: Vector, u: Vector, i: int {:trigger NN(n, u)[i], NN(n, v)} {:trigger NN(n, u)[i], Distance(v, u)} {:trigger NN(n, u)[i], CompatibleInput(v, n)} | |n[|n| - 1]| == |L| && AreLipBounds(n, L) && 0 <= i < |L| && |v| == |u| && CompatibleInput(v, n) && Distance(v, u) <= e && v' == NN(n, v) && i != x :: NN(n, u)[i] < NN(n, u)[x];
  }

  lemma ProveRobustHelper(v': Vector, e: real, L: seq<real>, x: int)
    requires |v'| == |L|
    requires x == ArgMax(v')
    requires forall n: NeuralNetwork, v: Vector, u: Vector, i: int {:trigger L[i], NN(n, u), NN(n, v)} {:trigger L[i], NN(n, v), Distance(v, u)} {:trigger L[i], Distance(v, u), CompatibleInput(v, n)} {:trigger L[i], Distance(v, u), AreLipBounds(n, L)} | |n[|n| - 1]| == |L| && AreLipBounds(n, L) && 0 <= i < |L| && |v| == |u| && CompatibleInput(v, n) && Distance(v, u) <= e :: Abs(NN(n, v)[i] - NN(n, u)[i]) <= L[i] * e
    ensures forall n: NeuralNetwork, v: Vector, u: Vector {:trigger NN(n, u), NN(n, v)[x]} {:trigger NN(n, v), Distance(v, u)} {:trigger Distance(v, u), CompatibleInput(v, n)} {:trigger Distance(v, u), AreLipBounds(n, L)} | |n[|n| - 1]| == |L| && AreLipBounds(n, L) && |v| == |u| && CompatibleInput(v, n) && Distance(v, u) <= e :: Abs(NN(n, v)[x] - NN(n, u)[x]) <= L[x] * e
    decreases v', e, L, x
  {
  }

  ghost predicate Robust(v: Vector, v': Vector, e: real, n: NeuralNetwork)
    requires CompatibleInput(v, n)
    requires NN(n, v) == v'
    decreases v, v', e, n
  {
    forall u: Vector {:trigger NN(n, u)} {:trigger Distance(v, u)} {:trigger |u|} | |v| == |u| && Distance(v, u) <= e :: 
      Classification(v') == Classification(NN(n, u))
  }

  function Classification(v: Vector): int
    decreases v
  {
    ArgMax(v)
  }

  function ArgMax(xs: Vector): (r: int)
    ensures 0 <= r < |xs|
    ensures forall i: int {:trigger xs[i]} :: 0 <= i < |xs| ==> xs[r] >= xs[i]
    ensures forall i: int {:trigger xs[i]} :: 0 <= i < |xs| ==> xs[r] == xs[i] ==> r <= i
    decreases xs
  {
    ArgMaxHelper(xs).0
  }

  function ArgMaxHelper(xs: Vector): (r: (int, real))
    requires |xs| > 0
    ensures 0 <= r.0 < |xs|
    ensures xs[r.0] == r.1
    ensures forall i: int {:trigger xs[i]} :: 0 <= i < |xs| ==> r.1 >= xs[i]
    ensures forall i: int {:trigger xs[i]} :: 0 <= i < |xs| ==> r.1 == xs[i] ==> r.0 <= i
    decreases xs
  {
    if |xs| == 1 || ArgMaxHelper(xs[0 .. |xs| - 1]).1 < xs[|xs| - 1] then
      (|xs| - 1, xs[|xs| - 1])
    else
      ArgMaxHelper(xs[0 .. |xs| - 1])
  }

  ghost predicate AreLipBounds(n: NeuralNetwork, L: seq<real>)
    requires |L| == |n[|n| - 1]|
    decreases n, L
  {
    forall i: int {:trigger L[i]} | 0 <= i < |L| :: 
      IsLipBound(n, L[i], i)
  }

  ghost predicate AreMarginLipBounds(n: NeuralNetwork, L: seq<seq<real>>)
    requires |L| == |n[|n| - 1]|
    decreases n, L
  {
    forall i: int, k: int {:trigger L[i][k]} | 0 <= i < |L| && 0 <= k < |L| && i != k :: 
      IsMarginLipBound(n, L[i][k], i, k)
  }

  ghost predicate IsLipBound(n: NeuralNetwork, l: real, i: int)
    requires 0 <= i < |n[|n| - 1]|
    decreases n, l, i
  {
    forall v: Vector, u: Vector {:trigger Distance(v, u)} {:trigger NN(n, u), NN(n, v)} {:trigger NN(n, u), CompatibleInput(v, n)} {:trigger NN(n, v), CompatibleInput(u, n)} {:trigger CompatibleInput(u, n), CompatibleInput(v, n)} | CompatibleInput(v, n) && CompatibleInput(u, n) :: 
      Abs(NN(n, v)[i] - NN(n, u)[i]) <= l * Distance(v, u)
  }

  ghost predicate IsMarginLipBound(n: NeuralNetwork, l: real, i: int, j: int)
    requires 0 <= i < |n[|n| - 1]|
    requires 0 <= j < |n[|n| - 1]|
    requires i != j
    decreases n, l, i, j
  {
    forall v: Vector, u: Vector {:trigger Distance(v, u)} {:trigger NN(n, u), NN(n, v)} {:trigger NN(n, u), CompatibleInput(v, n)} {:trigger NN(n, v), CompatibleInput(u, n)} {:trigger CompatibleInput(u, n), CompatibleInput(v, n)} | CompatibleInput(v, n) && CompatibleInput(u, n) :: 
      Abs(Abs(NN(n, v)[i] - NN(n, v)[j]) - Abs(NN(n, u)[i] - NN(n, u)[j])) <= l * Distance(v, u)
  }

  method GenMarginLipBounds(L: LipschitzBounds, n: NeuralNetwork, s: seq<real>)
      returns (r: seq<seq<real>>)
    requires |s| == |n|
    requires forall i: int {:trigger n[i]} {:trigger s[i]} | 0 <= i < |s| :: IsSpecNormUpperBound(s[i], n[i])
    ensures |r| == |n[|n| - 1]|
    ensures forall i: int, k: int {:trigger r[i][k]} | 0 <= i < |r| && 0 <= k < |r| :: 0.0 <= r[i][k]
    ensures AreMarginLipBounds(n, r)
    decreases L, n, s
  {
    r := [];
    var i := 0;
    while i < |n[|n| - 1]|
      invariant 0 <= i <= |n[|n| - 1]|
      invariant |r| == i
      invariant forall j: int {:trigger r[j]} | 0 <= j < i :: forall k: int {:trigger r[j][k]} | 0 <= k < |n[|n| - 1]| && i != k :: 0.0 <= r[j][k] && IsMarginLipBound(n, r[j][k], j, k)
      decreases |n[|n| - 1]| - i
    {
      var k := 0;
      var bound: seq<real> := [];
      while k < |n[|n| - 1]|
        decreases |n[|n| - 1]| - k
      {
        if k == i {
          bound := bound + [0.0];
        } else {
          var b := GenMarginLipBound(L, n, i, k, s);
          bound := bound + [b];
        }
        k := k + 1;
      }
      r := r + [bound];
      i := i + 1;
    }
    assert AreMarginLipBounds(n, r);
  }

  method GenLipBounds(L: LipschitzBounds, n: NeuralNetwork, s: seq<real>)
      returns (r: seq<real>)
    requires |s| == |n|
    requires forall i: int {:trigger n[i]} {:trigger s[i]} | 0 <= i < |s| :: IsSpecNormUpperBound(s[i], n[i])
    ensures |r| == |n[|n| - 1]|
    ensures forall i: int {:trigger r[i]} | 0 <= i < |r| :: 0.0 <= r[i]
    ensures AreLipBounds(n, r)
    decreases L, n, s
  {
    r := [];
    var i := 0;
    while i < |n[|n| - 1]|
      invariant 0 <= i <= |n[|n| - 1]|
      invariant |r| == i
      invariant forall j: int {:trigger r[j]} | 0 <= j < i :: 0.0 <= r[j] && IsLipBound(n, r[j], j)
      decreases |n[|n| - 1]| - i
    {
      var bound := GenLipBound(L, n, i, s);
      r := r + [bound];
      i := i + 1;
      assert forall j: int {:trigger r[j]} | 0 <= j < i :: IsLipBound(n, r[j], j) by {
        assert forall j: int {:trigger r[j]} | 0 <= j < i - 1 :: IsLipBound(n, r[j], j);
        assert IsLipBound(n, r[i - 1], i - 1);
      }
    }
    assert AreLipBounds(n, r);
  }

  method GenLipBound(L: LipschitzBounds, n: NeuralNetwork, l: int, s: seq<real>)
      returns (r: real)
    requires |s| == |n|
    requires 0 <= l < |n[|n| - 1]|
    requires forall i: int {:trigger n[i]} {:trigger s[i]} | 0 <= i < |s| :: IsSpecNormUpperBound(s[i], n[i])
    ensures IsLipBound(n, r, l)
    ensures r >= 0.0
    decreases L, n, l, s
  {
    var trimmedLayer := [n[|n| - 1][l]];
    var trimmedSpecNorm := L.GramIterationSimple(trimmedLayer);
    var n' := n[..|n| - 1] + [trimmedLayer];
    var s' := s[..|s| - 1] + [trimmedSpecNorm];
    r := Product(s');
    PositiveProduct(s');
    forall v: Vector, u: Vector | |v| == |u| && CompatibleInput(v, n') {
      SpecNormProductIsLipBound(n', v, u, s');
    }
    forall v: Vector, u: Vector | |v| == |u| && CompatibleInput(v, n') {
      LogitLipBounds(n, n', v, u, l);
    }
  }

  method GenMarginLipBound(L: LipschitzBounds, n: NeuralNetwork, l: int, k: int, s: seq<real>)
      returns (r: real)
    requires |s| == |n|
    requires 0 <= l < |n[|n| - 1]|
    requires 0 <= k < |n[|n| - 1]|
    requires l != k
    requires forall i: int {:trigger n[i]} {:trigger s[i]} | 0 <= i < |s| :: IsSpecNormUpperBound(s[i], n[i])
    ensures IsLipBound(n, r, l)
    ensures r >= 0.0
    decreases L, n, l, k, s
  {
    var vl := n[|n| - 1][l];
    var vk := n[|n| - 1][k];
    var trimmedLayerV := Minus(vl, vk);
    var trimmedLayer := [trimmedLayerV];
    var trimmedSpecNorm := L2UpperBound(trimmedLayerV);
    var n' := n[..|n| - 1] + [trimmedLayer];
    var s' := s[..|s| - 1] + [trimmedSpecNorm];
    r := Product(s');
    PositiveProduct(s');
  }

  lemma /*{:_inductionTrigger Product(s), NN(n, u), NN(n, v)}*/ /*{:_inductionTrigger Product(s), NN(n, u), |v|}*/ /*{:_inductionTrigger Product(s), NN(n, v), CompatibleInput(u, n)}*/ /*{:_inductionTrigger Product(s), NN(n, v), |u|}*/ /*{:_inductionTrigger Product(s), CompatibleInput(u, n), CompatibleInput(v, n)}*/ /*{:_inductionTrigger Product(s), CompatibleInput(u, n), |v|}*/ /*{:_inductionTrigger Product(s), CompatibleInput(v, n), |u|}*/ /*{:_inductionTrigger Product(s), |n|, |u|, |v|}*/ /*{:_inductionTrigger NN(n, u), NN(n, v), |s|}*/ /*{:_inductionTrigger NN(n, u), |s|, |v|}*/ /*{:_inductionTrigger NN(n, v), CompatibleInput(u, n), |s|}*/ /*{:_inductionTrigger NN(n, v), |s|, |u|}*/ /*{:_inductionTrigger CompatibleInput(u, n), CompatibleInput(v, n), |s|}*/ /*{:_inductionTrigger CompatibleInput(u, n), |s|, |v|}*/ /*{:_inductionTrigger CompatibleInput(v, n), |s|, |u|}*/ /*{:_inductionTrigger |n|, |s|, |u|, |v|}*/ /*{:_induction n, v, u, s}*/ SpecNormProductIsLipBound(n: NeuralNetwork, v: Vector, u: Vector, s: seq<real>)
    requires |v| == |u| && |s| == |n|
    requires CompatibleInput(v, n) && CompatibleInput(u, n)
    requires forall i: int {:trigger n[i]} {:trigger s[i]} | 0 <= i < |s| :: IsSpecNormUpperBound(s[i], n[i])
    ensures Distance(NN(n, v), NN(n, u)) <= Product(s) * Distance(v, u)
    decreases n, v, u, s
  {
    if |n| == 1 {
      SpecNormIsLayerLipBound(n[0], v, u, s[0]);
      reveal Product();
    } else {
      SpecNormIsLayerLipBound(n[0], v, u, s[0]);
      ghost var n0 := n[..|n| - 1];
      ghost var s0 := s[..|s| - 1];
      assert |s0| == |n0|;
      SpecNormProductIsLipBound(n0, v, u, s0);
      ghost var n' := n[|n| - 1];
      ghost var s' := s[|s| - 1];
      ghost var v' := NN(n0, v);
      ghost var u' := NN(n0, u);
      SpecNormIsLayerLipBound(n', v', u', s');
      reveal NN();
      assert Distance(NN(n, v), NN(n, u)) <= s' * Distance(v', u');
      assert Distance(v', u') <= Product(s0) * Distance(v, u);
      MultiplicationInequality(n, v, u, v', u', s0, s');
      ProductDef(s, s0, s');
      MultiplyBothSides(s, s0, s', v, u);
    }
  }

  lemma /*{:_inductionTrigger Product(s0), Product(s)}*/ /*{:_induction s, s0}*/ MultiplyBothSides(s: seq<real>, s0: seq<real>, s': real, v: Vector, u: Vector)
    requires |v| == |u|
    requires Product(s) == s' * Product(s0)
    ensures Product(s) * Distance(v, u) == s' * Product(s0) * Distance(v, u)
    decreases s, s0, s', v, u
  {
  }

  lemma /*{:_inductionTrigger Product(s0), NN(n, u), NN(n, v)}*/ /*{:_inductionTrigger Product(s0), NN(n, u), |v|}*/ /*{:_inductionTrigger Product(s0), NN(n, v), CompatibleInput(u, n)}*/ /*{:_inductionTrigger Product(s0), NN(n, v), |u|}*/ /*{:_inductionTrigger Product(s0), CompatibleInput(u, n), CompatibleInput(v, n)}*/ /*{:_inductionTrigger Product(s0), CompatibleInput(u, n), |v|}*/ /*{:_inductionTrigger Product(s0), CompatibleInput(v, n), |u|}*/ /*{:_induction n, v, u, s0}*/ MultiplicationInequality(n: NeuralNetwork, v: Vector, u: Vector, v': Vector, u': Vector, s0: seq<real>, s': real)
    requires |v| == |u|
    requires |v'| == |u'|
    requires s' >= 0.0
    requires CompatibleInput(v, n) && CompatibleInput(u, n)
    requires Distance(NN(n, v), NN(n, u)) <= s' * Distance(v', u')
    requires Distance(v', u') <= Product(s0) * Distance(v, u)
    ensures Distance(NN(n, v), NN(n, u)) <= s' * Product(s0) * Distance(v, u)
    decreases n, v, u, v', u', s0, s'
  {
  }

  lemma /*{:_inductionTrigger NN(n, u), NN(n', v)}*/ /*{:_inductionTrigger NN(n, v), NN(n', u)}*/ /*{:_inductionTrigger NN(n', u), CompatibleInput(v, n)}*/ /*{:_inductionTrigger NN(n', v), CompatibleInput(u, n)}*/ /*{:_induction n, n', v, u}*/ LogitLipBounds(n: NeuralNetwork, n': NeuralNetwork, v: Vector, u: Vector, l: int)
    requires |v| == |u|
    requires |n| == |n'|
    requires CompatibleInput(v, n)
    requires CompatibleInput(u, n)
    requires 0 <= l < |n[|n| - 1]|
    requires n' == n[..|n| - 1] + [[n[|n| - 1][l]]]
    ensures Distance(NN(n', v), NN(n', u)) == Abs(NN(n, v)[l] - NN(n, u)[l])
    decreases n, n', v, u, l
  {
    TrimmedNN(n, n', v, l);
    TrimmedNN(n, n', u, l);
    NormOfOneDimensionIsAbs();
  }

  lemma /*{:_inductionTrigger NN(n, v), NN(n', v)}*/ /*{:_inductionTrigger CompatibleInput(v, n'), CompatibleInput(v, n)}*/ /*{:_induction n, n', v}*/ TrimmedNN(n: NeuralNetwork, n': NeuralNetwork, v: Vector, l: int)
    requires 0 <= l < |n[|n| - 1]|
    requires CompatibleInput(v, n) && CompatibleInput(v, n')
    requires |n| == |n'|
    requires n' == n[..|n| - 1] + [[n[|n| - 1][l]]]
    ensures NN(n', v) == [NN(n, v)[l]]
    decreases n, n', v, l
  {
    assert n' == n[..|n| - 1] + [[n[|n| - 1][l]]];
    reveal NN();
  }

  lemma SpecNormIsLayerLipBound(m: Matrix, v: Vector, u: Vector, s: real)
    requires |m[0]| == |v| == |u|
    requires IsSpecNormUpperBound(s, m)
    ensures Distance(Layer(m, v), Layer(m, u)) <= s * Distance(v, u)
    decreases m, v, u, s
  {
    SpecNormIsMvLipBound(m, v, u, s);
    SmallerRelu(MV(m, v), MV(m, u));
  }

  lemma /*{:_inductionTrigger MV(m, u), MV(m, v)}*/ /*{:_inductionTrigger |m[0]|, |u|, |v|}*/ /*{:_induction m, v, u}*/ SpecNormIsMvLipBound(m: Matrix, v: Vector, u: Vector, s: real)
    requires |v| == |u| == |m[0]|
    requires IsSpecNormUpperBound(s, m)
    ensures Distance(MV(m, v), MV(m, u)) <= s * Distance(v, u)
    decreases m, v, u, s
  {
    SpecNormPropertyHoldsForDifferenceVectors(m, s, v, u);
    MvIsDistributive(m, v, u);
  }

  lemma /*{:_inductionTrigger Distance(v, u), IsSpecNormUpperBound(s, m)}*/ /*{:_inductionTrigger Distance(v, u), m[0]}*/ /*{:_inductionTrigger Minus(v, u), IsSpecNormUpperBound(s, m)}*/ /*{:_inductionTrigger Minus(v, u), m[0]}*/ /*{:_inductionTrigger |m[0]|, |u|, |v|}*/ /*{:_induction m, v, u}*/ SpecNormPropertyHoldsForDifferenceVectors(m: Matrix, s: real, v: Vector, u: Vector)
    requires |v| == |u| == |m[0]|
    requires IsSpecNormUpperBound(s, m)
    ensures L2(MV(m, Minus(v, u))) <= s * Distance(v, u)
    decreases m, s, v, u
  {
  }

  lemma /*{:_inductionTrigger Minus(MV(m, v), MV(m, u))}*/ /*{:_inductionTrigger MV(m, Minus(v, u))}*/ /*{:_inductionTrigger |u|, |v|, |m[0]|}*/ /*{:_induction m, v, u}*/ MvIsDistributive(m: Matrix, v: Vector, u: Vector)
    requires |m[0]| == |v| == |u|
    ensures MV(m, Minus(v, u)) == Minus(MV(m, v), MV(m, u))
    decreases m, v, u
  {
    for i: int := 0 to |m|
      invariant forall j: int {:trigger m[j]} | 0 <= j < i :: Dot(m[j], Minus(v, u)) == Dot(m[j], v) - Dot(m[j], u)
    {
      DotIsDistributive(m[i], v, u);
    }
  }

  lemma /*{:_inductionTrigger Minus(u, w), |v|}*/ /*{:_inductionTrigger |w|, |u|, |v|}*/ /*{:_induction v, u, w}*/ DotIsDistributive(v: Vector, u: Vector, w: Vector)
    requires |v| == |u| == |w|
    ensures Dot(v, Minus(u, w)) == Dot(v, u) - Dot(v, w)
    decreases v, u, w
  {
    reveal Dot();
    if |v| == 1 {
    } else {
      DotIsDistributive(v[1..], u[1..], w[1..]);
      assert Minus(u, w)[1..] == Minus(u[1..], w[1..]);
    }
  }

  lemma SmallerRelu(v: Vector, u: Vector)
    requires |v| == |u|
    ensures Distance(ApplyRelu(v), ApplyRelu(u)) <= Distance(v, u)
    decreases v, u
  {
    SmallerL2Norm(Minus(ApplyRelu(v), ApplyRelu(u)), Minus(v, u));
  }

  lemma SmallerL2Norm(v: Vector, u: Vector)
    requires |v| == |u|
    requires forall i: int {:trigger u[i]} {:trigger v[i]} :: 0 <= i < |v| ==> Abs(v[i]) <= Abs(u[i])
    ensures L2(v) <= L2(u)
    decreases v, u
  {
    reveal L2();
    SmallerApplySquare(v, u);
    MonotonicSum(Apply(v, Square), Apply(u, Square));
    MonotonicSqrt(Sum(Apply(v, Square)), Sum(Apply(u, Square)));
  }

  lemma /*{:_inductionTrigger Apply(u, Square), Apply(v, Square)}*/ /*{:_inductionTrigger Apply(u, Square), |v|}*/ /*{:_inductionTrigger Apply(v, Square), |u|}*/ /*{:_inductionTrigger |u|, |v|}*/ /*{:_induction v, u}*/ SmallerApplySquare(v: Vector, u: Vector)
    requires |v| == |u|
    requires forall i: int {:trigger u[i]} {:trigger v[i]} | 0 <= i < |v| :: Abs(v[i]) <= Abs(u[i])
    ensures forall i: int {:trigger Apply(u, Square)[i]} {:trigger Apply(v, Square)[i]} | 0 <= i < |v| :: Apply(v, Square)[i] <= Apply(u, Square)[i]
    decreases v, u
  {
    ghost var i := 0;
    while i < |v|
      invariant i <= |v|
      invariant forall j: int {:trigger Apply(u, Square)[j]} {:trigger Apply(v, Square)[j]} | 0 <= j < i :: Apply(v, Square)[j] <= Apply(u, Square)[j]
      decreases |v| - i
    {
      MonotonicSquare(v[i], u[i]);
      i := i + 1;
    }
  }

  import opened BasicArithmetic

  type Vector = v: seq<real>
    | |v| > 0
    witness [0.0]

  type Matrix = m: seq<Vector>
    | |m| > 0 && |m[0]| > 0 && forall i: int, j: int :: 0 <= i < |m| && 0 <= j < |m| ==> |m[i]| == |m[j]|
    witness [NonEmptyVector()]

  type NeuralNetwork = n: seq<Matrix>
    | |n| > 0 && forall i: int :: 0 <= i < |n| - 1 ==> |n[i]| == |n[i + 1][0]|
    witness [NonEmptyMatrix()]

  class LipschitzBounds {
    var GRAM_ITERATIONS: nat

    constructor (G: nat)
      decreases G
    {
      GRAM_ITERATIONS := G;
    }

    method GramIterationSimple(G: Matrix) returns (s: real)
      ensures IsSpecNormUpperBound(s, G)
      decreases G
    {
      var i := 0;
      var G' := G;
      while i != GRAM_ITERATIONS
        invariant 0 <= i <= GRAM_ITERATIONS
        invariant SpecNorm(G) <= Power2Root(SpecNorm(G'), i)
        decreases if i <= GRAM_ITERATIONS then GRAM_ITERATIONS - i else i - GRAM_ITERATIONS
      {
        if DEBUG {
          print ""{ \""debug_msg\"": \""Gram iteration for matrix of size "", |G|, ""x"", |G[0]|, "". Iteration "", i + 1, "" of "", GRAM_ITERATIONS, ""\"" },\n"";
        }
        Assumption1(G');
        Power2RootMonotonic(SpecNorm(G'), Sqrt(SpecNorm(MM(Transpose(G'), G'))), i);
        if DEBUG {
          print ""{ \""debug_msg\"": \""Gram iteration calling Transpose...\"" },\n"";
        }
        var GT := Transpose(G');
        if DEBUG {
          print ""{ \""debug_msg\"": \""Gram iteration Transpose done; calling MM...\"" },\n"";
        }
        G' := MM(GT, G');
        if DEBUG {
          print ""{ \""debug_msg\"": \""Gram iteration calling MM done.\"" },\n"";
        }
        Power2RootDef(SpecNorm(G'), i);
        i := i + 1;
      }
      if DEBUG {
        print ""{ \""debug_msg\"": \""Gram iteration done iterating\"" },\n"";
      }
      Assumption2(G');
      Power2RootMonotonic(SpecNorm(G'), FrobeniusNorm(G'), GRAM_ITERATIONS);
      if DEBUG {
        print ""{ \""debug_msg\"": \""Gram iteration computing frobenius norm upper bound...\"" },\n"";
      }
      s := FrobeniusNormUpperBound(G');
      Power2RootMonotonic(FrobeniusNorm(G'), s, GRAM_ITERATIONS);
      if DEBUG {
        print ""{ \""debug_msg\"": \""Gram iteration computing square root upper bound...\"" },\n"";
      }
      s := Power2RootUpperBound(s, GRAM_ITERATIONS);
      SpecNormUpperBoundProperty(s, G);
      if DEBUG {
        print ""{ \""debug_msg\"": \""Gram iteration done\"" },\n"";
      }
    }
  }
}

module StringUtils {
  method ParseReal(s: string) returns (r: real)
    requires IsReal(s)
    decreases s
  {
    var neg: bool := false;
    var i: int := 0;
    if s[i] == '-' {
      neg := true;
      i := i + 1;
    }
    r := ParseDigit(s[i]) as real;
    i := i + 1;
    var periodIndex: int := 1;
    while i < |s|
      decreases |s| - i
    {
      if IsDigit(s[i]) {
        r := r * 10.0 + ParseDigit(s[i]) as real;
      } else {
        periodIndex := i;
      }
      i := i + 1;
    }
    i := 0;
    while i < |s| - periodIndex - 1
      decreases |s| - periodIndex - 1 - i
    {
      r := r / 10.0;
      i := i + 1;
    }
    if neg {
      r := r * -1.0;
    }
  }

  method ParseInt(s: string) returns (r: int)
    requires IsInt(s)
    decreases s
  {
    var neg: bool := false;
    var i: int := 0;
    if s[i] == '-' {
      neg := true;
      i := i + 1;
    }
    r := ParseDigit(s[i]);
    i := i + 1;
    var periodIndex: int := 1;
    while i < |s|
      decreases |s| - i
    {
      if IsDigit(s[i]) {
        r := r * 10 + ParseDigit(s[i]);
      }
      i := i + 1;
    }
    if neg {
      r := r * -1;
    }
  }

  function ParseDigit(x: char): int
    requires IsDigit(x)
    decreases x
  {
    if x == '0' then
      0
    else if x == '1' then
      1
    else if x == '2' then
      2
    else if x == '3' then
      3
    else if x == '4' then
      4
    else if x == '5' then
      5
    else if x == '6' then
      6
    else if x == '7' then
      7
    else if x == '8' then
      8
    else
      9
  }

  predicate IsReal(s: string)
    decreases s
  {
    |s| >= 3 &&
    (IsDigit(s[0]) || (s[0] == '-' && IsDigit(s[1]))) &&
    IsDigit(s[|s| - 1]) &&
    exists i: int {:trigger s[i]} :: 
      0 <= i < |s| &&
      s[i] == '.' &&
      forall j: int {:trigger s[j]} :: 
        1 <= j < |s| &&
        j != i ==>
          IsDigit(s[j])
  }

  predicate IsInt(s: string)
    decreases s
  {
    |s| >= 1 &&
    (IsDigit(s[0]) || (|s| >= 2 && s[0] == '-' && IsDigit(s[1]))) &&
    IsDigit(s[|s| - 1]) &&
    forall j: int {:trigger s[j]} :: 
      1 <= j < |s| ==>
        IsDigit(s[j])
  }

  predicate IsDigit(x: char)
    decreases x
  {
    x == '0' || x == '1' || x == '2' || x == '3' || x == '4' || x == '5' || x == '6' || x == '7' || x == '8' || x == '9'
  }

  method Split(xs: string, x: char) returns (r: seq<string>)
    ensures |r| == |Indices(xs, x)| + 1
    ensures Indices(xs, x) == [] ==> r == [xs]
    ensures Indices(xs, x) != [] ==> r[0] == xs[..Indices(xs, x)[0]] && r[|r| - 1] == xs[Indices(xs, x)[|Indices(xs, x)| - 1]..][1..] && forall i: int, _t#0: int {:trigger Indices(xs, x)[i], Indices(xs, x)[_t#0]} {:trigger Indices(xs, x)[_t#0], r[i]} | _t#0 == i - 1 :: 1 <= i && i < |Indices(xs, x)| ==> r[i] == xs[Indices(xs, x)[_t#0] + 1 .. Indices(xs, x)[i]]
    decreases xs, x
  {
    var splits := Indices(xs, x);
    if splits == [] {
      return [xs];
    }
    r := [xs[..splits[0]]];
    var i := 1;
    while i < |splits|
      invariant 1 <= i <= |splits|
      invariant |r| == i
      invariant r[0] == xs[..splits[0]]
      invariant forall j: int, _t#0: int {:trigger splits[j], splits[_t#0]} {:trigger splits[_t#0], r[j]} | _t#0 == j - 1 :: 1 <= j && j < i ==> r[j] == xs[splits[_t#0] + 1 .. splits[j]]
      decreases |splits| - i
    {
      r := r + [xs[splits[i - 1] + 1 .. splits[i]]];
      i := i + 1;
    }
    r := r + [xs[splits[|splits| - 1]..][1..]];
  }

  function Indices(xs: string, x: char): (r: seq<int>)
    ensures forall i: int {:trigger r[i]} :: (0 <= i < |r| ==> 0 <= r[i]) && (0 <= i < |r| ==> r[i] < |xs|) && (0 <= i < |r| ==> xs[r[i]] == x)
    ensures forall i: int {:trigger i in r} {:trigger xs[i]} :: 0 <= i < |xs| && xs[i] == x ==> i in r
    ensures forall i: int, j: int {:trigger r[j], r[i]} :: 0 <= i < |r| && 0 <= j < |r| && i != j ==> r[i] != r[j]
    ensures forall i: int, j: int {:trigger r[j], r[i]} :: 0 <= i < j < |r| ==> r[i] < r[j]
    decreases xs, x
  {
    if |xs| == 0 then
      []
    else if xs[|xs| - 1] == x then
      Indices(xs[..|xs| - 1], x) + [|xs| - 1]
    else
      Indices(xs[..|xs| - 1], x)
  }
}

module {:options ""-functionSyntax:4""} FileIO {
  method ReadBytesFromFile(path: string) returns (res: Result<seq<bv8>, string>)
    decreases path
  {
    var isError, bytesRead, errorMsg := INTERNAL_ReadBytesFromFile(path);
    return if isError then Failure(errorMsg) else Success(bytesRead);
  }

  method WriteBytesToFile(path: string, bytes: seq<bv8>) returns (res: Result<(), string>)
    decreases path, bytes
  {
    var isError, errorMsg := INTERNAL_WriteBytesToFile(path, bytes);
    return if isError then Failure(errorMsg) else Success(());
  }

  method {:extern ""DafnyLibraries.FileIO"", ""INTERNAL_ReadBytesFromFile""} INTERNAL_ReadBytesFromFile(path: string)
      returns (isError: bool, bytesRead: seq<bv8>, errorMsg: string)
    decreases path

  method {:extern ""DafnyLibraries.FileIO"", ""INTERNAL_WriteBytesToFile""} INTERNAL_WriteBytesToFile(path: string, bytes: seq<bv8>)
      returns (isError: bool, errorMsg: string)
    decreases path, bytes

  import opened Wrappers

  export
    provides ReadBytesFromFile, WriteBytesToFile, Wrappers

}

module {:options ""-functionSyntax:4""} Wrappers {
  function Need<E>(condition: bool, error: E): (result: Outcome<E>)
    decreases condition
  {
    if condition then
      Pass
    else
      Fail(error)
  }

  datatype Option<+T> = None | Some(value: T) {
    function ToResult(): Result<T, string>
      decreases this
    {
      match this
      case Some(v) =>
        Success(v)
      case None() =>
        Failure(""Option is None"")
    }

    function ToResult'<R>(error: R): Result<T, R>
      decreases this
    {
      match this
      case Some(v) =>
        Success(v)
      case None() =>
        Failure(error)
    }

    function UnwrapOr(default: T): T
      decreases this
    {
      match this
      case Some(v) =>
        v
      case None() =>
        default
    }

    predicate IsFailure()
      decreases this
    {
      None?
    }

    function PropagateFailure<U>(): Option<U>
      requires None?
      decreases this
    {
      None
    }

    function Extract(): T
      requires Some?
      decreases this
    {
      value
    }
  }

  datatype Result<+T, +R> = Success(value: T) | Failure(error: R) {
    function ToOption(): Option<T>
      decreases this
    {
      match this
      case Success(s) =>
        Some(s)
      case Failure(e) =>
        None()
    }

    function UnwrapOr(default: T): T
      decreases this
    {
      match this
      case Success(s) =>
        s
      case Failure(e) =>
        default
    }

    predicate IsFailure()
      decreases this
    {
      Failure?
    }

    function PropagateFailure<U>(): Result<U, R>
      requires Failure?
      decreases this
    {
      Failure(this.error)
    }

    function MapFailure<NewR>(reWrap: R -> NewR): Result<T, NewR>
      decreases this
    {
      match this
      case Success(s) =>
        Success(s)
      case Failure(e) =>
        Failure(reWrap(e))
    }

    function Extract(): T
      requires Success?
      decreases this
    {
      value
    }
  }

  datatype Outcome<E> = Pass | Fail(error: E) {
    predicate IsFailure()
      decreases this
    {
      Fail?
    }

    function PropagateFailure<U>(): Result<U, E>
      requires Fail?
      decreases this
    {
      Failure(this.error)
    }
  }
}
")]

//-----------------------------------------------------------------------------
//
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------

// When --include-runtime is true, this file is directly prepended
// to the output program. We have to avoid these using directives in that case
// since they can only appear before any other declarations.
// The DafnyRuntime.csproj file is the only place that ISDAFNYRUNTIMELIB is defined,
// so these are only active when building the C# DafnyRuntime.dll library.
#if ISDAFNYRUNTIMELIB
using System; // for Func
using System.Numerics;
using System.Collections;
#endif

namespace DafnyAssembly {
  [AttributeUsage(AttributeTargets.Assembly)]
  public class DafnySourceAttribute : Attribute {
    public readonly string dafnySourceText;
    public DafnySourceAttribute(string txt) { dafnySourceText = txt; }
  }
}

namespace Dafny {
  using System.Collections.Generic;
  using System.Collections.Immutable;
  using System.Linq;

  // Similar to System.Text.Rune, which would be perfect to use
  // except that it isn't available in the platforms we support
  // (.NET Standard 2.0 and .NET Framework 4.5.2)
  public readonly struct Rune : IComparable, IComparable<Rune>, IEquatable<Rune> {

    private readonly uint _value;

    public Rune(int value)
      : this((uint)value) {
    }

    public Rune(uint value) {
      if (!(value < 0xD800 || (0xE000 <= value && value < 0x11_0000))) {
        throw new ArgumentException();
      }

      _value = value;
    }

    public static bool IsRune(BigInteger i) {
      return (0 <= i && i < 0xD800) || (0xE000 <= i && i < 0x11_0000);
    }

    public int Value => (int)_value;

    public bool Equals(Rune other) => this == other;

    public override bool Equals(object obj) => (obj is Rune other) && Equals(other);

    public override int GetHashCode() => Value;

    // Values are always between 0 and 0x11_0000, so overflow isn't possible
    public int CompareTo(Rune other) => this.Value - other.Value;

    int IComparable.CompareTo(object obj) {
      switch (obj) {
        case null:
          return 1; // non-null ("this") always sorts after null
        case Rune other:
          return CompareTo(other);
        default:
          throw new ArgumentException();
      }
    }

    public static bool operator ==(Rune left, Rune right) => left._value == right._value;

    public static bool operator !=(Rune left, Rune right) => left._value != right._value;

    public static bool operator <(Rune left, Rune right) => left._value < right._value;

    public static bool operator <=(Rune left, Rune right) => left._value <= right._value;

    public static bool operator >(Rune left, Rune right) => left._value > right._value;

    public static bool operator >=(Rune left, Rune right) => left._value >= right._value;

    public static explicit operator Rune(int value) => new Rune(value);
    public static explicit operator Rune(BigInteger value) => new Rune((uint)value);

    // Defined this way to be consistent with System.Text.Rune,
    // but note that Dafny will use Helpers.ToString(rune),
    // which will print in the style of a character literal instead.
    public override string ToString() {
      return char.ConvertFromUtf32(Value);
    }

    // Replacement for String.EnumerateRunes() from newer platforms
    public static IEnumerable<Rune> Enumerate(string s) {
      var sLength = s.Length;
      for (var i = 0; i < sLength; i++) {
        if (char.IsHighSurrogate(s[i])) {
          if (char.IsLowSurrogate(s[i + 1])) {
            yield return (Rune)char.ConvertToUtf32(s[i], s[i + 1]);
            i++;
          } else {
            throw new ArgumentException();
          }
        } else if (char.IsLowSurrogate(s[i])) {
          throw new ArgumentException();
        } else {
          yield return (Rune)s[i];
        }
      }
    }
  }

  public interface ISet<out T> {
    int Count { get; }
    long LongCount { get; }
    IEnumerable<T> Elements { get; }
    IEnumerable<ISet<T>> AllSubsets { get; }
    bool Contains<G>(G t);
    bool EqualsAux(ISet<object> other);
    ISet<U> DowncastClone<U>(Func<T, U> converter);
  }

  public class Set<T> : ISet<T> {
    readonly ImmutableHashSet<T> setImpl;
    readonly bool containsNull;
    Set(ImmutableHashSet<T> d, bool containsNull) {
      this.setImpl = d;
      this.containsNull = containsNull;
    }

    public static readonly ISet<T> Empty = new Set<T>(ImmutableHashSet<T>.Empty, false);

    private static readonly TypeDescriptor<ISet<T>> _TYPE = new Dafny.TypeDescriptor<ISet<T>>(Empty);
    public static TypeDescriptor<ISet<T>> _TypeDescriptor() {
      return _TYPE;
    }

    public static ISet<T> FromElements(params T[] values) {
      return FromCollection(values);
    }

    public static Set<T> FromISet(ISet<T> s) {
      return s as Set<T> ?? FromCollection(s.Elements);
    }

    public static Set<T> FromCollection(IEnumerable<T> values) {
      var d = ImmutableHashSet<T>.Empty.ToBuilder();
      var containsNull = false;
      foreach (T t in values) {
        if (t == null) {
          containsNull = true;
        } else {
          d.Add(t);
        }
      }

      return new Set<T>(d.ToImmutable(), containsNull);
    }

    public static ISet<T> FromCollectionPlusOne(IEnumerable<T> values, T oneMoreValue) {
      var d = ImmutableHashSet<T>.Empty.ToBuilder();
      var containsNull = false;
      if (oneMoreValue == null) {
        containsNull = true;
      } else {
        d.Add(oneMoreValue);
      }

      foreach (T t in values) {
        if (t == null) {
          containsNull = true;
        } else {
          d.Add(t);
        }
      }

      return new Set<T>(d.ToImmutable(), containsNull);
    }

    public ISet<U> DowncastClone<U>(Func<T, U> converter) {
      if (this is ISet<U> th) {
        return th;
      } else {
        var d = ImmutableHashSet<U>.Empty.ToBuilder();
        foreach (var t in this.setImpl) {
          var u = converter(t);
          d.Add(u);
        }

        return new Set<U>(d.ToImmutable(), this.containsNull);
      }
    }

    public int Count {
      get { return this.setImpl.Count + (containsNull ? 1 : 0); }
    }

    public long LongCount {
      get { return this.setImpl.Count + (containsNull ? 1 : 0); }
    }

    public IEnumerable<T> Elements {
      get {
        if (containsNull) {
          yield return default(T);
        }

        foreach (var t in this.setImpl) {
          yield return t;
        }
      }
    }

    /// <summary>
    /// This is an inefficient iterator for producing all subsets of "this".
    /// </summary>
    public IEnumerable<ISet<T>> AllSubsets {
      get {
        // Start by putting all set elements into a list, but don't include null
        var elmts = new List<T>();
        elmts.AddRange(this.setImpl);
        var n = elmts.Count;
        var which = new bool[n];
        var s = ImmutableHashSet<T>.Empty.ToBuilder();
        while (true) {
          // yield both the subset without null and, if null is in the original set, the subset with null included
          var ihs = s.ToImmutable();
          yield return new Set<T>(ihs, false);
          if (containsNull) {
            yield return new Set<T>(ihs, true);
          }

          // "add 1" to "which", as if doing a carry chain.  For every digit changed, change the membership of the corresponding element in "s".
          int i = 0;
          for (; i < n && which[i]; i++) {
            which[i] = false;
            s.Remove(elmts[i]);
          }

          if (i == n) {
            // we have cycled through all the subsets
            break;
          }

          which[i] = true;
          s.Add(elmts[i]);
        }
      }
    }

    public bool Equals(ISet<T> other) {
      if (ReferenceEquals(this, other)) {
        return true;
      }

      if (other == null || Count != other.Count) {
        return false;
      }

      foreach (var elmt in Elements) {
        if (!other.Contains(elmt)) {
          return false;
        }
      }

      return true;
    }

    public override bool Equals(object other) {
      if (other is ISet<T>) {
        return Equals((ISet<T>)other);
      }

      var th = this as ISet<object>;
      var oth = other as ISet<object>;
      if (th != null && oth != null) {
        // We'd like to obtain the more specific type parameter U for oth's type ISet<U>.
        // We do that by making a dynamically dispatched call, like:
        //     oth.Equals(this)
        // The hope is then that its comparison "this is ISet<U>" (that is, the first "if" test
        // above, but in the call "oth.Equals(this)") will be true and the non-virtual Equals
        // can be called. However, such a recursive call to "oth.Equals(this)" could turn
        // into infinite recursion. Therefore, we instead call "oth.EqualsAux(this)", which
        // performs the desired type test, but doesn't recurse any further.
        return oth.EqualsAux(th);
      } else {
        return false;
      }
    }

    public bool EqualsAux(ISet<object> other) {
      var s = other as ISet<T>;
      if (s != null) {
        return Equals(s);
      } else {
        return false;
      }
    }

    public override int GetHashCode() {
      var hashCode = 1;
      if (containsNull) {
        hashCode = hashCode * (Dafny.Helpers.GetHashCode(default(T)) + 3);
      }

      foreach (var t in this.setImpl) {
        hashCode = hashCode * (Dafny.Helpers.GetHashCode(t) + 3);
      }

      return hashCode;
    }

    public override string ToString() {
      var s = "{";
      var sep = "";
      if (containsNull) {
        s += sep + Dafny.Helpers.ToString(default(T));
        sep = ", ";
      }

      foreach (var t in this.setImpl) {
        s += sep + Dafny.Helpers.ToString(t);
        sep = ", ";
      }

      return s + "}";
    }
    public static bool IsProperSubsetOf(ISet<T> th, ISet<T> other) {
      return th.Count < other.Count && IsSubsetOf(th, other);
    }
    public static bool IsSubsetOf(ISet<T> th, ISet<T> other) {
      if (other.Count < th.Count) {
        return false;
      }
      foreach (T t in th.Elements) {
        if (!other.Contains(t)) {
          return false;
        }
      }
      return true;
    }
    public static bool IsDisjointFrom(ISet<T> th, ISet<T> other) {
      ISet<T> a, b;
      if (th.Count < other.Count) {
        a = th; b = other;
      } else {
        a = other; b = th;
      }
      foreach (T t in a.Elements) {
        if (b.Contains(t)) {
          return false;
        }
      }
      return true;
    }
    public bool Contains<G>(G t) {
      return t == null ? containsNull : t is T && this.setImpl.Contains((T)(object)t);
    }
    public static ISet<T> Union(ISet<T> th, ISet<T> other) {
      var a = FromISet(th);
      var b = FromISet(other);
      return new Set<T>(a.setImpl.Union(b.setImpl), a.containsNull || b.containsNull);
    }
    public static ISet<T> Intersect(ISet<T> th, ISet<T> other) {
      var a = FromISet(th);
      var b = FromISet(other);
      return new Set<T>(a.setImpl.Intersect(b.setImpl), a.containsNull && b.containsNull);
    }
    public static ISet<T> Difference(ISet<T> th, ISet<T> other) {
      var a = FromISet(th);
      var b = FromISet(other);
      return new Set<T>(a.setImpl.Except(b.setImpl), a.containsNull && !b.containsNull);
    }
  }

  public interface IMultiSet<out T> {
    bool IsEmpty { get; }
    int Count { get; }
    long LongCount { get; }
    BigInteger ElementCount { get; }
    IEnumerable<T> Elements { get; }
    IEnumerable<T> UniqueElements { get; }
    bool Contains<G>(G t);
    BigInteger Select<G>(G t);
    IMultiSet<T> Update<G>(G t, BigInteger i);
    bool EqualsAux(IMultiSet<object> other);
    IMultiSet<U> DowncastClone<U>(Func<T, U> converter);
  }

  public class MultiSet<T> : IMultiSet<T> {
    readonly ImmutableDictionary<T, BigInteger> dict;
    readonly BigInteger occurrencesOfNull;  // stupidly, a Dictionary in .NET cannot use "null" as a key
    MultiSet(ImmutableDictionary<T, BigInteger>.Builder d, BigInteger occurrencesOfNull) {
      dict = d.ToImmutable();
      this.occurrencesOfNull = occurrencesOfNull;
    }
    public static readonly MultiSet<T> Empty = new MultiSet<T>(ImmutableDictionary<T, BigInteger>.Empty.ToBuilder(), BigInteger.Zero);

    private static readonly TypeDescriptor<IMultiSet<T>> _TYPE = new Dafny.TypeDescriptor<IMultiSet<T>>(Empty);
    public static TypeDescriptor<IMultiSet<T>> _TypeDescriptor() {
      return _TYPE;
    }

    public static MultiSet<T> FromIMultiSet(IMultiSet<T> s) {
      return s as MultiSet<T> ?? FromCollection(s.Elements);
    }
    public static MultiSet<T> FromElements(params T[] values) {
      var d = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      var occurrencesOfNull = BigInteger.Zero;
      foreach (T t in values) {
        if (t == null) {
          occurrencesOfNull++;
        } else {
          if (!d.TryGetValue(t, out var i)) {
            i = BigInteger.Zero;
          }
          d[t] = i + 1;
        }
      }
      return new MultiSet<T>(d, occurrencesOfNull);
    }

    public static MultiSet<T> FromCollection(IEnumerable<T> values) {
      var d = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      var occurrencesOfNull = BigInteger.Zero;
      foreach (T t in values) {
        if (t == null) {
          occurrencesOfNull++;
        } else {
          if (!d.TryGetValue(t,
                out var i)) {
            i = BigInteger.Zero;
          }

          d[t] = i + 1;
        }
      }

      return new MultiSet<T>(d,
        occurrencesOfNull);
    }

    public static MultiSet<T> FromSeq(ISequence<T> values) {
      var d = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      var occurrencesOfNull = BigInteger.Zero;
      foreach (var t in values) {
        if (t == null) {
          occurrencesOfNull++;
        } else {
          if (!d.TryGetValue(t,
                out var i)) {
            i = BigInteger.Zero;
          }

          d[t] = i + 1;
        }
      }

      return new MultiSet<T>(d,
        occurrencesOfNull);
    }
    public static MultiSet<T> FromSet(ISet<T> values) {
      var d = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      var containsNull = false;
      foreach (T t in values.Elements) {
        if (t == null) {
          containsNull = true;
        } else {
          d[t] = BigInteger.One;
        }
      }
      return new MultiSet<T>(d, containsNull ? BigInteger.One : BigInteger.Zero);
    }
    public IMultiSet<U> DowncastClone<U>(Func<T, U> converter) {
      if (this is IMultiSet<U> th) {
        return th;
      } else {
        var d = ImmutableDictionary<U, BigInteger>.Empty.ToBuilder();
        foreach (var item in this.dict) {
          var k = converter(item.Key);
          d.Add(k, item.Value);
        }
        return new MultiSet<U>(d, this.occurrencesOfNull);
      }
    }

    public bool Equals(IMultiSet<T> other) {
      return IsSubsetOf(this, other) && IsSubsetOf(other, this);
    }
    public override bool Equals(object other) {
      if (other is IMultiSet<T>) {
        return Equals((IMultiSet<T>)other);
      }
      var th = this as IMultiSet<object>;
      var oth = other as IMultiSet<object>;
      if (th != null && oth != null) {
        // See comment in Set.Equals
        return oth.EqualsAux(th);
      } else {
        return false;
      }
    }

    public bool EqualsAux(IMultiSet<object> other) {
      var s = other as IMultiSet<T>;
      if (s != null) {
        return Equals(s);
      } else {
        return false;
      }
    }

    public override int GetHashCode() {
      var hashCode = 1;
      if (occurrencesOfNull > 0) {
        var key = Dafny.Helpers.GetHashCode(default(T));
        key = (key << 3) | (key >> 29) ^ occurrencesOfNull.GetHashCode();
        hashCode = hashCode * (key + 3);
      }
      foreach (var kv in dict) {
        var key = Dafny.Helpers.GetHashCode(kv.Key);
        key = (key << 3) | (key >> 29) ^ kv.Value.GetHashCode();
        hashCode = hashCode * (key + 3);
      }
      return hashCode;
    }
    public override string ToString() {
      var s = "multiset{";
      var sep = "";
      for (var i = BigInteger.Zero; i < occurrencesOfNull; i++) {
        s += sep + Dafny.Helpers.ToString(default(T));
        sep = ", ";
      }
      foreach (var kv in dict) {
        var t = Dafny.Helpers.ToString(kv.Key);
        for (var i = BigInteger.Zero; i < kv.Value; i++) {
          s += sep + t;
          sep = ", ";
        }
      }
      return s + "}";
    }
    public static bool IsProperSubsetOf(IMultiSet<T> th, IMultiSet<T> other) {
      // Be sure to use ElementCount to avoid casting into 32 bits
      // integers that could lead to overflows (see https://github.com/dafny-lang/dafny/issues/5554)
      return th.ElementCount < other.ElementCount && IsSubsetOf(th, other);
    }
    public static bool IsSubsetOf(IMultiSet<T> th, IMultiSet<T> other) {
      var a = FromIMultiSet(th);
      var b = FromIMultiSet(other);
      if (b.occurrencesOfNull < a.occurrencesOfNull) {
        return false;
      }
      foreach (T t in a.dict.Keys) {
        if (b.dict.ContainsKey(t)) {
          if (b.dict[t] < a.dict[t]) {
            return false;
          }
        } else {
          if (a.dict[t] != BigInteger.Zero) {
            return false;
          }
        }
      }
      return true;
    }
    public static bool IsDisjointFrom(IMultiSet<T> th, IMultiSet<T> other) {
      foreach (T t in th.UniqueElements) {
        if (other.Contains(t)) {
          return false;
        }
      }
      return true;
    }

    public bool Contains<G>(G t) {
      return Select(t) != 0;
    }
    public BigInteger Select<G>(G t) {
      if (t == null) {
        return occurrencesOfNull;
      }

      if (t is T && dict.TryGetValue((T)(object)t, out var m)) {
        return m;
      } else {
        return BigInteger.Zero;
      }
    }
    public IMultiSet<T> Update<G>(G t, BigInteger i) {
      if (Select(t) == i) {
        return this;
      } else if (t == null) {
        var r = dict.ToBuilder();
        return new MultiSet<T>(r, i);
      } else {
        var r = dict.ToBuilder();
        r[(T)(object)t] = i;
        return new MultiSet<T>(r, occurrencesOfNull);
      }
    }
    public static IMultiSet<T> Union(IMultiSet<T> th, IMultiSet<T> other) {
      if (th.IsEmpty) {
        return other;
      } else if (other.IsEmpty) {
        return th;
      }
      var a = FromIMultiSet(th);
      var b = FromIMultiSet(other);
      var r = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      foreach (T t in a.dict.Keys) {
        if (!r.TryGetValue(t, out var i)) {
          i = BigInteger.Zero;
        }
        r[t] = i + a.dict[t];
      }
      foreach (T t in b.dict.Keys) {
        if (!r.TryGetValue(t, out var i)) {
          i = BigInteger.Zero;
        }
        r[t] = i + b.dict[t];
      }
      return new MultiSet<T>(r, a.occurrencesOfNull + b.occurrencesOfNull);
    }
    public static IMultiSet<T> Intersect(IMultiSet<T> th, IMultiSet<T> other) {
      if (th.IsEmpty) {
        return th;
      } else if (other.IsEmpty) {
        return other;
      }
      var a = FromIMultiSet(th);
      var b = FromIMultiSet(other);
      var r = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      foreach (T t in a.dict.Keys) {
        if (b.dict.ContainsKey(t)) {
          r.Add(t, a.dict[t] < b.dict[t] ? a.dict[t] : b.dict[t]);
        }
      }
      return new MultiSet<T>(r, a.occurrencesOfNull < b.occurrencesOfNull ? a.occurrencesOfNull : b.occurrencesOfNull);
    }
    public static IMultiSet<T> Difference(IMultiSet<T> th, IMultiSet<T> other) { // \result == this - other
      if (other.IsEmpty) {
        return th;
      }
      var a = FromIMultiSet(th);
      var b = FromIMultiSet(other);
      var r = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      foreach (T t in a.dict.Keys) {
        if (!b.dict.ContainsKey(t)) {
          r.Add(t, a.dict[t]);
        } else if (b.dict[t] < a.dict[t]) {
          r.Add(t, a.dict[t] - b.dict[t]);
        }
      }
      return new MultiSet<T>(r, b.occurrencesOfNull < a.occurrencesOfNull ? a.occurrencesOfNull - b.occurrencesOfNull : BigInteger.Zero);
    }

    public bool IsEmpty { get { return occurrencesOfNull == 0 && dict.IsEmpty; } }

    public int Count {
      get { return (int)ElementCount; }
    }
    public long LongCount {
      get { return (long)ElementCount; }
    }

    public BigInteger ElementCount {
      get {
        // This is inefficient
        var c = occurrencesOfNull;
        foreach (var item in dict) {
          c += item.Value;
        }
        return c;
      }
    }

    public IEnumerable<T> Elements {
      get {
        for (var i = BigInteger.Zero; i < occurrencesOfNull; i++) {
          yield return default(T);
        }
        foreach (var item in dict) {
          for (var i = BigInteger.Zero; i < item.Value; i++) {
            yield return item.Key;
          }
        }
      }
    }

    public IEnumerable<T> UniqueElements {
      get {
        if (!occurrencesOfNull.IsZero) {
          yield return default(T);
        }
        foreach (var key in dict.Keys) {
          if (dict[key] != 0) {
            yield return key;
          }
        }
      }
    }
  }

  public interface IMap<out U, out V> {
    int Count { get; }
    long LongCount { get; }
    ISet<U> Keys { get; }
    ISet<V> Values { get; }
    IEnumerable<IPair<U, V>> ItemEnumerable { get; }
    bool Contains<G>(G t);
    /// <summary>
    /// Returns "true" iff "this is IMap<object, object>" and "this" equals "other".
    /// </summary>
    bool EqualsObjObj(IMap<object, object> other);
    IMap<UU, VV> DowncastClone<UU, VV>(Func<U, UU> keyConverter, Func<V, VV> valueConverter);
  }

  public class Map<U, V> : IMap<U, V> {
    readonly ImmutableDictionary<U, V> dict;
    readonly bool hasNullKey;  // true when "null" is a key of the Map
    readonly V nullValue;  // if "hasNullKey", the value that "null" maps to

    private Map(ImmutableDictionary<U, V>.Builder d, bool hasNullKey, V nullValue) {
      dict = d.ToImmutable();
      this.hasNullKey = hasNullKey;
      this.nullValue = nullValue;
    }
    public static readonly Map<U, V> Empty = new Map<U, V>(ImmutableDictionary<U, V>.Empty.ToBuilder(), false, default(V));

    private Map(ImmutableDictionary<U, V> d, bool hasNullKey, V nullValue) {
      dict = d;
      this.hasNullKey = hasNullKey;
      this.nullValue = nullValue;
    }

    private static readonly TypeDescriptor<IMap<U, V>> _TYPE = new Dafny.TypeDescriptor<IMap<U, V>>(Empty);
    public static TypeDescriptor<IMap<U, V>> _TypeDescriptor() {
      return _TYPE;
    }

    public static Map<U, V> FromElements(params IPair<U, V>[] values) {
      var d = ImmutableDictionary<U, V>.Empty.ToBuilder();
      var hasNullKey = false;
      var nullValue = default(V);
      foreach (var p in values) {
        if (p.Car == null) {
          hasNullKey = true;
          nullValue = p.Cdr;
        } else {
          d[p.Car] = p.Cdr;
        }
      }
      return new Map<U, V>(d, hasNullKey, nullValue);
    }
    public static Map<U, V> FromCollection(IEnumerable<IPair<U, V>> values) {
      var d = ImmutableDictionary<U, V>.Empty.ToBuilder();
      var hasNullKey = false;
      var nullValue = default(V);
      foreach (var p in values) {
        if (p.Car == null) {
          hasNullKey = true;
          nullValue = p.Cdr;
        } else {
          d[p.Car] = p.Cdr;
        }
      }
      return new Map<U, V>(d, hasNullKey, nullValue);
    }
    public static Map<U, V> FromIMap(IMap<U, V> m) {
      return m as Map<U, V> ?? FromCollection(m.ItemEnumerable);
    }
    public IMap<UU, VV> DowncastClone<UU, VV>(Func<U, UU> keyConverter, Func<V, VV> valueConverter) {
      if (this is IMap<UU, VV> th) {
        return th;
      } else {
        var d = ImmutableDictionary<UU, VV>.Empty.ToBuilder();
        foreach (var item in this.dict) {
          var k = keyConverter(item.Key);
          var v = valueConverter(item.Value);
          d.Add(k, v);
        }
        return new Map<UU, VV>(d, this.hasNullKey, (VV)(object)this.nullValue);
      }
    }
    public int Count {
      get { return dict.Count + (hasNullKey ? 1 : 0); }
    }
    public long LongCount {
      get { return dict.Count + (hasNullKey ? 1 : 0); }
    }

    public bool Equals(IMap<U, V> other) {
      if (ReferenceEquals(this, other)) {
        return true;
      }

      if (other == null || LongCount != other.LongCount) {
        return false;
      }

      if (hasNullKey) {
        if (!other.Contains(default(U)) || !object.Equals(nullValue, Select(other, default(U)))) {
          return false;
        }
      }

      foreach (var item in dict) {
        if (!other.Contains(item.Key) || !object.Equals(item.Value, Select(other, item.Key))) {
          return false;
        }
      }
      return true;
    }
    public bool EqualsObjObj(IMap<object, object> other) {
      if (ReferenceEquals(this, other)) {
        return true;
      }
      if (!(this is IMap<object, object>) || other == null || LongCount != other.LongCount) {
        return false;
      }
      var oth = Map<object, object>.FromIMap(other);
      if (hasNullKey) {
        if (!oth.Contains(default(U)) || !object.Equals(nullValue, Map<object, object>.Select(oth, default(U)))) {
          return false;
        }
      }
      foreach (var item in dict) {
        if (!other.Contains(item.Key) || !object.Equals(item.Value, Map<object, object>.Select(oth, item.Key))) {
          return false;
        }
      }
      return true;
    }
    public override bool Equals(object other) {
      // See comment in Set.Equals
      var m = other as IMap<U, V>;
      if (m != null) {
        return Equals(m);
      }
      var imapoo = other as IMap<object, object>;
      if (imapoo != null) {
        return EqualsObjObj(imapoo);
      } else {
        return false;
      }
    }

    public override int GetHashCode() {
      var hashCode = 1;
      if (hasNullKey) {
        var key = Dafny.Helpers.GetHashCode(default(U));
        key = (key << 3) | (key >> 29) ^ Dafny.Helpers.GetHashCode(nullValue);
        hashCode = hashCode * (key + 3);
      }
      foreach (var kv in dict) {
        var key = Dafny.Helpers.GetHashCode(kv.Key);
        key = (key << 3) | (key >> 29) ^ Dafny.Helpers.GetHashCode(kv.Value);
        hashCode = hashCode * (key + 3);
      }
      return hashCode;
    }
    public override string ToString() {
      var s = "map[";
      var sep = "";
      if (hasNullKey) {
        s += sep + Dafny.Helpers.ToString(default(U)) + " := " + Dafny.Helpers.ToString(nullValue);
        sep = ", ";
      }
      foreach (var kv in dict) {
        s += sep + Dafny.Helpers.ToString(kv.Key) + " := " + Dafny.Helpers.ToString(kv.Value);
        sep = ", ";
      }
      return s + "]";
    }
    public bool Contains<G>(G u) {
      return u == null ? hasNullKey : u is U && dict.ContainsKey((U)(object)u);
    }
    public static V Select(IMap<U, V> th, U index) {
      // the following will throw an exception if "index" in not a key of the map
      var m = FromIMap(th);
      return index == null && m.hasNullKey ? m.nullValue : m.dict[index];
    }
    public static IMap<U, V> Update(IMap<U, V> th, U index, V val) {
      var m = FromIMap(th);
      var d = m.dict.ToBuilder();
      if (index == null) {
        return new Map<U, V>(d, true, val);
      } else {
        d[index] = val;
        return new Map<U, V>(d, m.hasNullKey, m.nullValue);
      }
    }

    public static IMap<U, V> Merge(IMap<U, V> th, IMap<U, V> other) {
      var a = FromIMap(th);
      var b = FromIMap(other);
      ImmutableDictionary<U, V> d = a.dict.SetItems(b.dict);
      return new Map<U, V>(d, a.hasNullKey || b.hasNullKey, b.hasNullKey ? b.nullValue : a.nullValue);
    }

    public static IMap<U, V> Subtract(IMap<U, V> th, ISet<U> keys) {
      var a = FromIMap(th);
      ImmutableDictionary<U, V> d = a.dict.RemoveRange(keys.Elements);
      return new Map<U, V>(d, a.hasNullKey && !keys.Contains<object>(null), a.nullValue);
    }

    public ISet<U> Keys {
      get {
        if (hasNullKey) {
          return Dafny.Set<U>.FromCollectionPlusOne(dict.Keys, default(U));
        } else {
          return Dafny.Set<U>.FromCollection(dict.Keys);
        }
      }
    }
    public ISet<V> Values {
      get {
        if (hasNullKey) {
          return Dafny.Set<V>.FromCollectionPlusOne(dict.Values, nullValue);
        } else {
          return Dafny.Set<V>.FromCollection(dict.Values);
        }
      }
    }

    public IEnumerable<IPair<U, V>> ItemEnumerable {
      get {
        if (hasNullKey) {
          yield return new Pair<U, V>(default(U), nullValue);
        }
        foreach (KeyValuePair<U, V> kvp in dict) {
          yield return new Pair<U, V>(kvp.Key, kvp.Value);
        }
      }
    }

    public static ISet<_System._ITuple2<U, V>> Items(IMap<U, V> m) {
      var result = new HashSet<_System._ITuple2<U, V>>();
      foreach (var item in m.ItemEnumerable) {
        result.Add(_System.Tuple2<U, V>.create(item.Car, item.Cdr));
      }
      return Dafny.Set<_System._ITuple2<U, V>>.FromCollection(result);
    }
  }

  public interface ISequence<out T> : IEnumerable<T> {
    long LongCount { get; }
    int Count { get; }
    [Obsolete("Use CloneAsArray() instead of Elements (both perform a copy).")]
    T[] Elements { get; }
    T[] CloneAsArray();
    IEnumerable<T> UniqueElements { get; }
    T Select(ulong index);
    T Select(long index);
    T Select(uint index);
    T Select(int index);
    T Select(BigInteger index);
    bool Contains<G>(G g);
    ISequence<T> Take(long m);
    ISequence<T> Take(ulong n);
    ISequence<T> Take(BigInteger n);
    ISequence<T> Drop(long m);
    ISequence<T> Drop(ulong n);
    ISequence<T> Drop(BigInteger n);
    ISequence<T> Subsequence(long lo, long hi);
    ISequence<T> Subsequence(long lo, ulong hi);
    ISequence<T> Subsequence(long lo, BigInteger hi);
    ISequence<T> Subsequence(ulong lo, long hi);
    ISequence<T> Subsequence(ulong lo, ulong hi);
    ISequence<T> Subsequence(ulong lo, BigInteger hi);
    ISequence<T> Subsequence(BigInteger lo, long hi);
    ISequence<T> Subsequence(BigInteger lo, ulong hi);
    ISequence<T> Subsequence(BigInteger lo, BigInteger hi);
    bool EqualsAux(ISequence<object> other);
    ISequence<U> DowncastClone<U>(Func<T, U> converter);
    string ToVerbatimString(bool asLiteral);
  }

  public abstract class Sequence<T> : ISequence<T> {
    public static readonly ISequence<T> Empty = new ArraySequence<T>(new T[0]);

    private static readonly TypeDescriptor<ISequence<T>> _TYPE = new Dafny.TypeDescriptor<ISequence<T>>(Empty);
    public static TypeDescriptor<ISequence<T>> _TypeDescriptor() {
      return _TYPE;
    }

    public static ISequence<T> Create(BigInteger length, System.Func<BigInteger, T> init) {
      var len = (int)length;
      var builder = ImmutableArray.CreateBuilder<T>(len);
      for (int i = 0; i < len; i++) {
        builder.Add(init(new BigInteger(i)));
      }
      return new ArraySequence<T>(builder.MoveToImmutable());
    }
    public static ISequence<T> FromArray(T[] values) {
      return new ArraySequence<T>(values);
    }
    public static ISequence<T> FromElements(params T[] values) {
      return new ArraySequence<T>(values);
    }
    public static ISequence<char> FromString(string s) {
      return new ArraySequence<char>(s.ToCharArray());
    }
    public static ISequence<Rune> UnicodeFromString(string s) {
      var runes = new List<Rune>();

      foreach (var rune in Rune.Enumerate(s)) {
        runes.Add(rune);
      }
      return new ArraySequence<Rune>(runes.ToArray());
    }

    public static ISequence<ISequence<char>> FromMainArguments(string[] args) {
      Dafny.ISequence<char>[] dafnyArgs = new Dafny.ISequence<char>[args.Length + 1];
      dafnyArgs[0] = Dafny.Sequence<char>.FromString("dotnet");
      for (var i = 0; i < args.Length; i++) {
        dafnyArgs[i + 1] = Dafny.Sequence<char>.FromString(args[i]);
      }

      return Sequence<ISequence<char>>.FromArray(dafnyArgs);
    }
    public static ISequence<ISequence<Rune>> UnicodeFromMainArguments(string[] args) {
      Dafny.ISequence<Rune>[] dafnyArgs = new Dafny.ISequence<Rune>[args.Length + 1];
      dafnyArgs[0] = Dafny.Sequence<Rune>.UnicodeFromString("dotnet");
      for (var i = 0; i < args.Length; i++) {
        dafnyArgs[i + 1] = Dafny.Sequence<Rune>.UnicodeFromString(args[i]);
      }

      return Sequence<ISequence<Rune>>.FromArray(dafnyArgs);
    }

    public ISequence<U> DowncastClone<U>(Func<T, U> converter) {
      if (this is ISequence<U> th) {
        return th;
      } else {
        var values = new U[this.LongCount];
        for (long i = 0; i < this.LongCount; i++) {
          var val = converter(this.Select(i));
          values[i] = val;
        }
        return new ArraySequence<U>(values);
      }
    }
    public static ISequence<T> Update(ISequence<T> sequence, long index, T t) {
      T[] tmp = sequence.CloneAsArray();
      tmp[index] = t;
      return new ArraySequence<T>(tmp);
    }
    public static ISequence<T> Update(ISequence<T> sequence, ulong index, T t) {
      return Update(sequence, (long)index, t);
    }
    public static ISequence<T> Update(ISequence<T> sequence, BigInteger index, T t) {
      return Update(sequence, (long)index, t);
    }
    public static bool EqualUntil(ISequence<T> left, ISequence<T> right, int n) {
      for (int i = 0; i < n; i++) {
        if (!Equals(left.Select(i), right.Select(i))) {
          return false;
        }
      }
      return true;
    }
    public static bool IsPrefixOf(ISequence<T> left, ISequence<T> right) {
      int n = left.Count;
      return n <= right.Count && EqualUntil(left, right, n);
    }
    public static bool IsProperPrefixOf(ISequence<T> left, ISequence<T> right) {
      int n = left.Count;
      return n < right.Count && EqualUntil(left, right, n);
    }
    public static ISequence<T> Concat(ISequence<T> left, ISequence<T> right) {
      if (left.Count == 0) {
        return right;
      }
      if (right.Count == 0) {
        return left;
      }
      return new ConcatSequence<T>(left, right);
    }
    // Make Count a public abstract instead of LongCount, since the "array size is limited to a total of 4 billion
    // elements, and to a maximum index of 0X7FEFFFFF". Therefore, as a protection, limit this to int32.
    // https://docs.microsoft.com/en-us/dotnet/api/system.array
    public abstract int Count { get; }
    public long LongCount {
      get { return Count; }
    }
    // ImmutableElements cannot be public in the interface since ImmutableArray<T> leads to a
    // "covariant type T occurs in invariant position" error. There do not appear to be interfaces for ImmutableArray<T>
    // that resolve this.
    internal abstract ImmutableArray<T> ImmutableElements { get; }

    public T[] Elements { get { return CloneAsArray(); } }

    public T[] CloneAsArray() {
      return ImmutableElements.ToArray();
    }

    public IEnumerable<T> UniqueElements {
      get {
        return Set<T>.FromCollection(ImmutableElements).Elements;
      }
    }

    public IEnumerator<T> GetEnumerator() {
      foreach (var el in ImmutableElements) {
        yield return el;
      }
    }

    IEnumerator IEnumerable.GetEnumerator() {
      return GetEnumerator();
    }

    public T Select(ulong index) {
      return ImmutableElements[checked((int)index)];
    }
    public T Select(long index) {
      return ImmutableElements[checked((int)index)];
    }
    public T Select(uint index) {
      return ImmutableElements[checked((int)index)];
    }
    public T Select(int index) {
      return ImmutableElements[index];
    }
    public T Select(BigInteger index) {
      return ImmutableElements[(int)index];
    }
    public bool Equals(ISequence<T> other) {
      return ReferenceEquals(this, other) || (Count == other.Count && EqualUntil(this, other, Count));
    }
    public override bool Equals(object other) {
      if (other is ISequence<T>) {
        return Equals((ISequence<T>)other);
      }
      var th = this as ISequence<object>;
      var oth = other as ISequence<object>;
      if (th != null && oth != null) {
        // see explanation in Set.Equals
        return oth.EqualsAux(th);
      } else {
        return false;
      }
    }
    public bool EqualsAux(ISequence<object> other) {
      var s = other as ISequence<T>;
      if (s != null) {
        return Equals(s);
      } else {
        return false;
      }
    }
    public override int GetHashCode() {
      ImmutableArray<T> elmts = ImmutableElements;
      // https://devblogs.microsoft.com/dotnet/please-welcome-immutablearrayt/
      if (elmts.IsDefaultOrEmpty) {
        return 0;
      }

      var hashCode = 0;
      for (var i = 0; i < elmts.Length; i++) {
        hashCode = (hashCode << 3) | (hashCode >> 29) ^ Dafny.Helpers.GetHashCode(elmts[i]);
      }
      return hashCode;
    }
    public override string ToString() {
      if (typeof(T) == typeof(char)) {
        return string.Concat(this);
      } else {
        return "[" + string.Join(", ", ImmutableElements.Select(Dafny.Helpers.ToString)) + "]";
      }
    }

    public string ToVerbatimString(bool asLiteral) {
      var builder = new System.Text.StringBuilder();
      if (asLiteral) {
        builder.Append('"');
      }
      foreach (var c in this) {
        var rune = (Rune)(object)c;
        if (asLiteral) {
          builder.Append(Helpers.EscapeCharacter(rune));
        } else {
          builder.Append(char.ConvertFromUtf32(rune.Value));
        }
      }
      if (asLiteral) {
        builder.Append('"');
      }
      return builder.ToString();
    }

    public bool Contains<G>(G g) {
      if (g == null || g is T) {
        var t = (T)(object)g;
        return ImmutableElements.Contains(t);
      }
      return false;
    }
    public ISequence<T> Take(long m) {
      return Subsequence(0, m);
    }
    public ISequence<T> Take(ulong n) {
      return Take((long)n);
    }
    public ISequence<T> Take(BigInteger n) {
      return Take((long)n);
    }
    public ISequence<T> Drop(long m) {
      return Subsequence(m, Count);
    }
    public ISequence<T> Drop(ulong n) {
      return Drop((long)n);
    }
    public ISequence<T> Drop(BigInteger n) {
      return Drop((long)n);
    }
    public ISequence<T> Subsequence(long lo, long hi) {
      if (lo == 0 && hi == Count) {
        return this;
      }
      int startingIndex = checked((int)lo);
      var length = checked((int)hi) - startingIndex;
      return new ArraySequence<T>(ImmutableArray.Create<T>(ImmutableElements, startingIndex, length));
    }
    public ISequence<T> Subsequence(long lo, ulong hi) {
      return Subsequence(lo, (long)hi);
    }
    public ISequence<T> Subsequence(long lo, BigInteger hi) {
      return Subsequence(lo, (long)hi);
    }
    public ISequence<T> Subsequence(ulong lo, long hi) {
      return Subsequence((long)lo, hi);
    }
    public ISequence<T> Subsequence(ulong lo, ulong hi) {
      return Subsequence((long)lo, (long)hi);
    }
    public ISequence<T> Subsequence(ulong lo, BigInteger hi) {
      return Subsequence((long)lo, (long)hi);
    }
    public ISequence<T> Subsequence(BigInteger lo, long hi) {
      return Subsequence((long)lo, hi);
    }
    public ISequence<T> Subsequence(BigInteger lo, ulong hi) {
      return Subsequence((long)lo, (long)hi);
    }
    public ISequence<T> Subsequence(BigInteger lo, BigInteger hi) {
      return Subsequence((long)lo, (long)hi);
    }
  }

  internal class ArraySequence<T> : Sequence<T> {
    private readonly ImmutableArray<T> elmts;

    internal ArraySequence(ImmutableArray<T> ee) {
      elmts = ee;
    }
    internal ArraySequence(T[] ee) {
      elmts = ImmutableArray.Create<T>(ee);
    }

    internal override ImmutableArray<T> ImmutableElements {
      get {
        return elmts;
      }
    }

    public override int Count {
      get {
        return elmts.Length;
      }
    }
  }

  internal class ConcatSequence<T> : Sequence<T> {
    // INVARIANT: Either left != null, right != null, and elmts's underlying array == null or
    // left == null, right == null, and elmts's underlying array != null
    internal volatile ISequence<T> left, right;
    internal ImmutableArray<T> elmts;
    private readonly int count;

    internal ConcatSequence(ISequence<T> left, ISequence<T> right) {
      this.left = left;
      this.right = right;
      this.count = left.Count + right.Count;
    }

    internal override ImmutableArray<T> ImmutableElements {
      get {
        // IsDefault returns true if the underlying array is a null reference
        // https://devblogs.microsoft.com/dotnet/please-welcome-immutablearrayt/
        if (elmts.IsDefault) {
          elmts = ComputeElements();
          // We don't need the original sequences anymore; let them be
          // garbage-collected
          left = null;
          right = null;
        }
        return elmts;
      }
    }

    public override int Count {
      get {
        return count;
      }
    }

    internal ImmutableArray<T> ComputeElements() {
      // Traverse the tree formed by all descendants which are ConcatSequences
      var ansBuilder = ImmutableArray.CreateBuilder<T>(count);
      var toVisit = new Stack<ISequence<T>>();
      var leftBuffer = left;
      var rightBuffer = right;
      if (left == null || right == null) {
        // elmts can't be .IsDefault while either left, or right are null
        return elmts;
      }
      toVisit.Push(rightBuffer);
      toVisit.Push(leftBuffer);

      while (toVisit.Count != 0) {
        var seq = toVisit.Pop();
        if (seq is ConcatSequence<T> cs && cs.elmts.IsDefault) {
          leftBuffer = cs.left;
          rightBuffer = cs.right;
          if (cs.left == null || cs.right == null) {
            // !cs.elmts.IsDefault, due to concurrent enumeration
            toVisit.Push(cs);
          } else {
            toVisit.Push(rightBuffer);
            toVisit.Push(leftBuffer);
          }
        } else {
          if (seq is Sequence<T> sq) {
            ansBuilder.AddRange(sq.ImmutableElements); // Optimized path for ImmutableArray
          } else {
            ansBuilder.AddRange(seq); // Slower path using IEnumerable
          }
        }
      }
      return ansBuilder.MoveToImmutable();
    }
  }

  public interface IPair<out A, out B> {
    A Car { get; }
    B Cdr { get; }
  }

  public class Pair<A, B> : IPair<A, B> {
    private A car;
    private B cdr;
    public A Car { get { return car; } }
    public B Cdr { get { return cdr; } }
    public Pair(A a, B b) {
      this.car = a;
      this.cdr = b;
    }
  }

  public class TypeDescriptor<T> {
    private readonly T initValue;
    public TypeDescriptor(T initValue) {
      this.initValue = initValue;
    }
    public T Default() {
      return initValue;
    }
  }

  public partial class Helpers {
    public static int GetHashCode<G>(G g) {
      return g == null ? 1001 : g.GetHashCode();
    }

    public static int ToIntChecked(BigInteger i, string msg) {
      if (i > Int32.MaxValue || i < Int32.MinValue) {
        if (msg == null) {
          msg = "value out of range for a 32-bit int";
        }

        throw new HaltException(msg + ": " + i);
      }
      return (int)i;
    }
    public static int ToIntChecked(long i, string msg) {
      if (i > Int32.MaxValue || i < Int32.MinValue) {
        if (msg == null) {
          msg = "value out of range for a 32-bit int";
        }

        throw new HaltException(msg + ": " + i);
      }
      return (int)i;
    }
    public static int ToIntChecked(int i, string msg) {
      return i;
    }

    public static string ToString<G>(G g) {
      if (g == null) {
        return "null";
      } else if (g is bool) {
        return (bool)(object)g ? "true" : "false";  // capitalize boolean literals like in Dafny
      } else if (g is Rune) {
        return "'" + EscapeCharacter((Rune)(object)g) + "'";
      } else {
        return g.ToString();
      }
    }

    public static string EscapeCharacter(Rune r) {
      switch (r.Value) {
        case '\n': return "\\n";
        case '\r': return "\\r";
        case '\t': return "\\t";
        case '\0': return "\\0";
        case '\'': return "\\'";
        case '\"': return "\\\"";
        case '\\': return "\\\\";
        default: return r.ToString();
      };
    }

    public static void Print<G>(G g) {
      System.Console.Write(ToString(g));
    }

    public static readonly TypeDescriptor<bool> BOOL = new TypeDescriptor<bool>(false);
    public static readonly TypeDescriptor<char> CHAR = new TypeDescriptor<char>('D');  // See CharType.DefaultValue in Dafny source code
    public static readonly TypeDescriptor<Rune> RUNE = new TypeDescriptor<Rune>(new Rune('D'));  // See CharType.DefaultValue in Dafny source code
    public static readonly TypeDescriptor<BigInteger> INT = new TypeDescriptor<BigInteger>(BigInteger.Zero);
    public static readonly TypeDescriptor<BigRational> REAL = new TypeDescriptor<BigRational>(BigRational.ZERO);
    public static readonly TypeDescriptor<byte> UINT8 = new TypeDescriptor<byte>(0);
    public static readonly TypeDescriptor<ushort> UINT16 = new TypeDescriptor<ushort>(0);
    public static readonly TypeDescriptor<uint> UINT32 = new TypeDescriptor<uint>(0);
    public static readonly TypeDescriptor<ulong> UINT64 = new TypeDescriptor<ulong>(0);

    public static TypeDescriptor<T> NULL<T>() where T : class {
      return new TypeDescriptor<T>(null);
    }

    public static TypeDescriptor<A[]> ARRAY<A>() {
      return new TypeDescriptor<A[]>(new A[0]);
    }

    public static bool Quantifier<T>(IEnumerable<T> vals, bool frall, System.Predicate<T> pred) {
      foreach (var u in vals) {
        if (pred(u) != frall) { return !frall; }
      }
      return frall;
    }
    // Enumerating other collections
    public static IEnumerable<bool> AllBooleans() {
      yield return false;
      yield return true;
    }
    public static IEnumerable<char> AllChars() {
      for (int i = 0; i < 0x1_0000; i++) {
        yield return (char)i;
      }
    }
    public static IEnumerable<Rune> AllUnicodeChars() {
      for (int i = 0; i < 0xD800; i++) {
        yield return new Rune(i);
      }
      for (int i = 0xE000; i < 0x11_0000; i++) {
        yield return new Rune(i);
      }
    }
    public static IEnumerable<BigInteger> AllIntegers() {
      yield return new BigInteger(0);
      for (var j = new BigInteger(1); ; j++) {
        yield return j;
        yield return -j;
      }
    }
    public static IEnumerable<BigInteger> IntegerRange(Nullable<BigInteger> lo, Nullable<BigInteger> hi) {
      if (lo == null) {
        for (var j = (BigInteger)hi; true;) {
          j--;
          yield return j;
        }
      } else if (hi == null) {
        for (var j = (BigInteger)lo; true; j++) {
          yield return j;
        }
      } else {
        for (var j = (BigInteger)lo; j < hi; j++) {
          yield return j;
        }
      }
    }
    public static IEnumerable<T> SingleValue<T>(T e) {
      yield return e;
    }
    // pre: b != 0
    // post: result == a/b, as defined by Euclidean Division (http://en.wikipedia.org/wiki/Modulo_operation)
    public static sbyte EuclideanDivision_sbyte(sbyte a, sbyte b) {
      return (sbyte)EuclideanDivision_int(a, b);
    }
    public static short EuclideanDivision_short(short a, short b) {
      return (short)EuclideanDivision_int(a, b);
    }
    public static int EuclideanDivision_int(int a, int b) {
      if (0 <= a) {
        if (0 <= b) {
          // +a +b: a/b
          return (int)(((uint)(a)) / ((uint)(b)));
        } else {
          // +a -b: -(a/(-b))
          return -((int)(((uint)(a)) / ((uint)(unchecked(-b)))));
        }
      } else {
        if (0 <= b) {
          // -a +b: -((-a-1)/b) - 1
          return -((int)(((uint)(-(a + 1))) / ((uint)(b)))) - 1;
        } else {
          // -a -b: ((-a-1)/(-b)) + 1
          return ((int)(((uint)(-(a + 1))) / ((uint)(unchecked(-b))))) + 1;
        }
      }
    }
    public static long EuclideanDivision_long(long a, long b) {
      if (0 <= a) {
        if (0 <= b) {
          // +a +b: a/b
          return (long)(((ulong)(a)) / ((ulong)(b)));
        } else {
          // +a -b: -(a/(-b))
          return -((long)(((ulong)(a)) / ((ulong)(unchecked(-b)))));
        }
      } else {
        if (0 <= b) {
          // -a +b: -((-a-1)/b) - 1
          return -((long)(((ulong)(-(a + 1))) / ((ulong)(b)))) - 1;
        } else {
          // -a -b: ((-a-1)/(-b)) + 1
          return ((long)(((ulong)(-(a + 1))) / ((ulong)(unchecked(-b))))) + 1;
        }
      }
    }
    public static BigInteger EuclideanDivision(BigInteger a, BigInteger b) {
      if (0 <= a.Sign) {
        if (0 <= b.Sign) {
          // +a +b: a/b
          return BigInteger.Divide(a, b);
        } else {
          // +a -b: -(a/(-b))
          return BigInteger.Negate(BigInteger.Divide(a, BigInteger.Negate(b)));
        }
      } else {
        if (0 <= b.Sign) {
          // -a +b: -((-a-1)/b) - 1
          return BigInteger.Negate(BigInteger.Divide(BigInteger.Negate(a) - 1, b)) - 1;
        } else {
          // -a -b: ((-a-1)/(-b)) + 1
          return BigInteger.Divide(BigInteger.Negate(a) - 1, BigInteger.Negate(b)) + 1;
        }
      }
    }
    // pre: b != 0
    // post: result == a%b, as defined by Euclidean Division (http://en.wikipedia.org/wiki/Modulo_operation)
    public static sbyte EuclideanModulus_sbyte(sbyte a, sbyte b) {
      return (sbyte)EuclideanModulus_int(a, b);
    }
    public static short EuclideanModulus_short(short a, short b) {
      return (short)EuclideanModulus_int(a, b);
    }
    public static int EuclideanModulus_int(int a, int b) {
      uint bp = (0 <= b) ? (uint)b : (uint)(unchecked(-b));
      if (0 <= a) {
        // +a: a % b'
        return (int)(((uint)a) % bp);
      } else {
        // c = ((-a) % b')
        // -a: b' - c if c > 0
        // -a: 0 if c == 0
        uint c = ((uint)(unchecked(-a))) % bp;
        return (int)(c == 0 ? c : bp - c);
      }
    }
    public static long EuclideanModulus_long(long a, long b) {
      ulong bp = (0 <= b) ? (ulong)b : (ulong)(unchecked(-b));
      if (0 <= a) {
        // +a: a % b'
        return (long)(((ulong)a) % bp);
      } else {
        // c = ((-a) % b')
        // -a: b' - c if c > 0
        // -a: 0 if c == 0
        ulong c = ((ulong)(unchecked(-a))) % bp;
        return (long)(c == 0 ? c : bp - c);
      }
    }
    public static BigInteger EuclideanModulus(BigInteger a, BigInteger b) {
      var bp = BigInteger.Abs(b);
      if (0 <= a.Sign) {
        // +a: a % b'
        return BigInteger.Remainder(a, bp);
      } else {
        // c = ((-a) % b')
        // -a: b' - c if c > 0
        // -a: 0 if c == 0
        var c = BigInteger.Remainder(BigInteger.Negate(a), bp);
        return c.IsZero ? c : BigInteger.Subtract(bp, c);
      }
    }

    public static U CastConverter<T, U>(T t) {
      return (U)(object)t;
    }

    public static Sequence<T> SeqFromArray<T>(T[] array) {
      return new ArraySequence<T>(array);
    }
    // In .NET version 4.5, it is possible to mark a method with "AggressiveInlining", which says to inline the
    // method if possible.  Method "ExpressionSequence" would be a good candidate for it:
    // [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.AggressiveInlining)]
    public static U ExpressionSequence<T, U>(T t, U u) {
      return u;
    }

    public static U Let<T, U>(T t, Func<T, U> f) {
      return f(t);
    }

    public static A Id<A>(A a) {
      return a;
    }

    public static void WithHaltHandling(Action action) {
      try {
        action();
      } catch (HaltException e) {
        Console.WriteLine("[Program halted] " + e.Message);
        // This is unfriendly given that Dafny's C# compiler will
        // invoke the compiled main method directly,
        // so we might be exiting the whole Dafny process here.
        // That's the best we can do until Dafny main methods support
        // a return value though (https://github.com/dafny-lang/dafny/issues/2699).
        // If we just set Environment.ExitCode here, the Dafny CLI
        // will just override that with 0.
        Environment.Exit(1);
      }
    }

    public static Rune AddRunes(Rune left, Rune right) {
      return (Rune)(left.Value + right.Value);
    }

    public static Rune SubtractRunes(Rune left, Rune right) {
      return (Rune)(left.Value - right.Value);
    }

    public static uint Bv32ShiftLeft(uint a, int amount) {
      return 32 <= amount ? 0 : a << amount;
    }
    public static ulong Bv64ShiftLeft(ulong a, int amount) {
      return 64 <= amount ? 0 : a << amount;
    }

    public static uint Bv32ShiftRight(uint a, int amount) {
      return 32 <= amount ? 0 : a >> amount;
    }
    public static ulong Bv64ShiftRight(ulong a, int amount) {
      return 64 <= amount ? 0 : a >> amount;
    }
  }

  public class BigOrdinal {
    public static bool IsLimit(BigInteger ord) {
      return ord == 0;
    }
    public static bool IsSucc(BigInteger ord) {
      return 0 < ord;
    }
    public static BigInteger Offset(BigInteger ord) {
      return ord;
    }
    public static bool IsNat(BigInteger ord) {
      return true;  // at run time, every ORDINAL is a natural number
    }
  }

  public struct BigRational {
    public static readonly BigRational ZERO = new BigRational(0);

    // We need to deal with the special case "num == 0 && den == 0", because
    // that's what C#'s default struct constructor will produce for BigRational. :(
    // To deal with it, we ignore "den" when "num" is 0.
    public readonly BigInteger num, den;  // invariant 1 <= den || (num == 0 && den == 0)

    public override string ToString() {
      if (num.IsZero || den.IsOne) {
        return string.Format("{0}.0", num);
      } else if (DividesAPowerOf10(den, out var factor, out var log10)) {
        var n = num * factor;
        string sign;
        string digits;
        if (n.Sign < 0) {
          sign = "-"; digits = (-n).ToString();
        } else {
          sign = ""; digits = n.ToString();
        }
        if (log10 < digits.Length) {
          var digitCount = digits.Length - log10;
          return string.Format("{0}{1}.{2}", sign, digits.Substring(0, digitCount), digits.Substring(digitCount));
        } else {
          return string.Format("{0}0.{1}{2}", sign, new string('0', log10 - digits.Length), digits);
        }
      } else {
        return string.Format("({0}.0 / {1}.0)", num, den);
      }
    }
    public static bool IsPowerOf10(BigInteger x, out int log10) {
      log10 = 0;
      if (x.IsZero) {
        return false;
      }
      while (true) {  // invariant: x != 0 && x * 10^log10 == old(x)
        if (x.IsOne) {
          return true;
        } else if (x % 10 == 0) {
          log10++;
          x /= 10;
        } else {
          return false;
        }
      }
    }
    /// <summary>
    /// If this method return true, then
    ///     10^log10 == factor * i
    /// Otherwise, factor and log10 should not be used.
    /// </summary>
    public static bool DividesAPowerOf10(BigInteger i, out BigInteger factor, out int log10) {
      factor = BigInteger.One;
      log10 = 0;
      if (i <= 0) {
        return false;
      }

      BigInteger ten = 10;
      BigInteger five = 5;
      BigInteger two = 2;

      // invariant: 1 <= i && i * 10^log10 == factor * old(i)
      while (i % ten == 0) {
        i /= ten;
        log10++;
      }

      while (i % five == 0) {
        i /= five;
        factor *= two;
        log10++;
      }
      while (i % two == 0) {
        i /= two;
        factor *= five;
        log10++;
      }

      return i == BigInteger.One;
    }

    public BigRational(int n) {
      num = new BigInteger(n);
      den = BigInteger.One;
    }
    public BigRational(uint n) {
      num = new BigInteger(n);
      den = BigInteger.One;
    }
    public BigRational(long n) {
      num = new BigInteger(n);
      den = BigInteger.One;
    }
    public BigRational(ulong n) {
      num = new BigInteger(n);
      den = BigInteger.One;
    }
    public BigRational(BigInteger n, BigInteger d) {
      // requires 1 <= d
      num = n;
      den = d;
    }
    /// <summary>
    /// Construct an exact rational representation of a double value.
    /// Throw an exception on NaN or infinite values. Does not support
    /// subnormal values, though it would be possible to extend it to.
    /// </summary>
    public BigRational(double n) {
      if (Double.IsNaN(n)) {
        throw new ArgumentException("Can't convert NaN to a rational.");
      }
      if (Double.IsInfinity(n)) {
        throw new ArgumentException(
          "Can't convert +/- infinity to a rational.");
      }

      // Double-specific values
      const int exptBias = 1023;
      const ulong signMask = 0x8000000000000000;
      const ulong exptMask = 0x7FF0000000000000;
      const ulong mantMask = 0x000FFFFFFFFFFFFF;
      const int mantBits = 52;
      ulong bits = BitConverter.ToUInt64(BitConverter.GetBytes(n), 0);

      // Generic conversion
      bool isNeg = (bits & signMask) != 0;
      int expt = ((int)((bits & exptMask) >> mantBits)) - exptBias;
      var mant = (bits & mantMask);

      if (expt == -exptBias && mant != 0) {
        throw new ArgumentException(
          "Can't convert a subnormal value to a rational (yet).");
      }

      var one = BigInteger.One;
      var negFactor = isNeg ? BigInteger.Negate(one) : one;
      var two = new BigInteger(2);
      var exptBI = BigInteger.Pow(two, Math.Abs(expt));
      var twoToMantBits = BigInteger.Pow(two, mantBits);
      var mantNum = negFactor * (twoToMantBits + new BigInteger(mant));
      if (expt == -exptBias && mant == 0) {
        num = den = 0;
      } else if (expt < 0) {
        num = mantNum;
        den = twoToMantBits * exptBI;
      } else {
        num = exptBI * mantNum;
        den = twoToMantBits;
      }
    }
    public BigInteger ToBigInteger() {
      if (num.IsZero || den.IsOne) {
        return num;
      } else if (0 < num.Sign) {
        return num / den;
      } else {
        return (num - den + 1) / den;
      }
    }

    public bool IsInteger() {
      var floored = new BigRational(this.ToBigInteger(), BigInteger.One);
      return this == floored;
    }

    /// <summary>
    /// Returns values such that aa/dd == a and bb/dd == b.
    /// </summary>
    private static void Normalize(BigRational a, BigRational b, out BigInteger aa, out BigInteger bb, out BigInteger dd) {
      if (a.num.IsZero) {
        aa = a.num;
        bb = b.num;
        dd = b.den;
      } else if (b.num.IsZero) {
        aa = a.num;
        dd = a.den;
        bb = b.num;
      } else {
        var gcd = BigInteger.GreatestCommonDivisor(a.den, b.den);
        var xx = a.den / gcd;
        var yy = b.den / gcd;
        // We now have a == a.num / (xx * gcd) and b == b.num / (yy * gcd).
        aa = a.num * yy;
        bb = b.num * xx;
        dd = a.den * yy;
      }
    }
    public int CompareTo(BigRational that) {
      // simple things first
      int asign = this.num.Sign;
      int bsign = that.num.Sign;
      if (asign < 0 && 0 <= bsign) {
        return -1;
      } else if (asign <= 0 && 0 < bsign) {
        return -1;
      } else if (bsign < 0 && 0 <= asign) {
        return 1;
      } else if (bsign <= 0 && 0 < asign) {
        return 1;
      }

      Normalize(this, that, out var aa, out var bb, out var dd);
      return aa.CompareTo(bb);
    }
    public int Sign {
      get {
        return num.Sign;
      }
    }
    public override int GetHashCode() {
      return num.GetHashCode() + 29 * den.GetHashCode();
    }
    public override bool Equals(object obj) {
      if (obj is BigRational) {
        return this == (BigRational)obj;
      } else {
        return false;
      }
    }
    public static bool operator ==(BigRational a, BigRational b) {
      return a.CompareTo(b) == 0;
    }
    public static bool operator !=(BigRational a, BigRational b) {
      return a.CompareTo(b) != 0;
    }
    public static bool operator >(BigRational a, BigRational b) {
      return a.CompareTo(b) > 0;
    }
    public static bool operator >=(BigRational a, BigRational b) {
      return a.CompareTo(b) >= 0;
    }
    public static bool operator <(BigRational a, BigRational b) {
      return a.CompareTo(b) < 0;
    }
    public static bool operator <=(BigRational a, BigRational b) {
      return a.CompareTo(b) <= 0;
    }
    public static BigRational operator +(BigRational a, BigRational b) {
      Normalize(a, b, out var aa, out var bb, out var dd);
      return new BigRational(aa + bb, dd);
    }
    public static BigRational operator -(BigRational a, BigRational b) {
      Normalize(a, b, out var aa, out var bb, out var dd);
      return new BigRational(aa - bb, dd);
    }
    public static BigRational operator -(BigRational a) {
      return new BigRational(-a.num, a.den);
    }
    public static BigRational operator *(BigRational a, BigRational b) {
      return new BigRational(a.num * b.num, a.den * b.den);
    }
    public static BigRational operator /(BigRational a, BigRational b) {
      // Compute the reciprocal of b
      BigRational bReciprocal;
      if (0 < b.num.Sign) {
        bReciprocal = new BigRational(b.den, b.num);
      } else {
        // this is the case b.num < 0
        bReciprocal = new BigRational(-b.den, -b.num);
      }
      return a * bReciprocal;
    }
  }

  public class HaltException : Exception {
    public HaltException(object message) : base(message.ToString()) {
    }
  }
}
// Dafny program systemModulePopulator.dfy compiled into C#
// To recompile, you will need the libraries
//     System.Runtime.Numerics.dll System.Collections.Immutable.dll
// but the 'dotnet' tool in .NET should pick those up automatically.
// Optionally, you may want to include compiler switches like
//     /debug /nowarn:162,164,168,183,219,436,1717,1718

#if ISDAFNYRUNTIMELIB
using System;
using System.Numerics;
using System.Collections;
#endif
#if ISDAFNYRUNTIMELIB
namespace Dafny {
  internal class ArrayHelpers {
    public static T[] InitNewArray1<T>(T z, BigInteger size0) {
      int s0 = (int)size0;
      T[] a = new T[s0];
      for (int i0 = 0; i0 < s0; i0++) {
        a[i0] = z;
      }
      return a;
    }
    public static T[,] InitNewArray2<T>(T z, BigInteger size0, BigInteger size1) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      T[,] a = new T[s0,s1];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          a[i0,i1] = z;
        }
      }
      return a;
    }
    public static T[,,] InitNewArray3<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      T[,,] a = new T[s0,s1,s2];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            a[i0,i1,i2] = z;
          }
        }
      }
      return a;
    }
    public static T[,,,] InitNewArray4<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      T[,,,] a = new T[s0,s1,s2,s3];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              a[i0,i1,i2,i3] = z;
            }
          }
        }
      }
      return a;
    }
    public static T[,,,,] InitNewArray5<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3, BigInteger size4) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      int s4 = (int)size4;
      T[,,,,] a = new T[s0,s1,s2,s3,s4];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              for (int i4 = 0; i4 < s4; i4++) {
                a[i0,i1,i2,i3,i4] = z;
              }
            }
          }
        }
      }
      return a;
    }
    public static T[,,,,,] InitNewArray6<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3, BigInteger size4, BigInteger size5) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      int s4 = (int)size4;
      int s5 = (int)size5;
      T[,,,,,] a = new T[s0,s1,s2,s3,s4,s5];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              for (int i4 = 0; i4 < s4; i4++) {
                for (int i5 = 0; i5 < s5; i5++) {
                  a[i0,i1,i2,i3,i4,i5] = z;
                }
              }
            }
          }
        }
      }
      return a;
    }
    public static T[,,,,,,] InitNewArray7<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3, BigInteger size4, BigInteger size5, BigInteger size6) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      int s4 = (int)size4;
      int s5 = (int)size5;
      int s6 = (int)size6;
      T[,,,,,,] a = new T[s0,s1,s2,s3,s4,s5,s6];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              for (int i4 = 0; i4 < s4; i4++) {
                for (int i5 = 0; i5 < s5; i5++) {
                  for (int i6 = 0; i6 < s6; i6++) {
                    a[i0,i1,i2,i3,i4,i5,i6] = z;
                  }
                }
              }
            }
          }
        }
      }
      return a;
    }
    public static T[,,,,,,,] InitNewArray8<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3, BigInteger size4, BigInteger size5, BigInteger size6, BigInteger size7) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      int s4 = (int)size4;
      int s5 = (int)size5;
      int s6 = (int)size6;
      int s7 = (int)size7;
      T[,,,,,,,] a = new T[s0,s1,s2,s3,s4,s5,s6,s7];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              for (int i4 = 0; i4 < s4; i4++) {
                for (int i5 = 0; i5 < s5; i5++) {
                  for (int i6 = 0; i6 < s6; i6++) {
                    for (int i7 = 0; i7 < s7; i7++) {
                      a[i0,i1,i2,i3,i4,i5,i6,i7] = z;
                    }
                  }
                }
              }
            }
          }
        }
      }
      return a;
    }
    public static T[,,,,,,,,] InitNewArray9<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3, BigInteger size4, BigInteger size5, BigInteger size6, BigInteger size7, BigInteger size8) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      int s4 = (int)size4;
      int s5 = (int)size5;
      int s6 = (int)size6;
      int s7 = (int)size7;
      int s8 = (int)size8;
      T[,,,,,,,,] a = new T[s0,s1,s2,s3,s4,s5,s6,s7,s8];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              for (int i4 = 0; i4 < s4; i4++) {
                for (int i5 = 0; i5 < s5; i5++) {
                  for (int i6 = 0; i6 < s6; i6++) {
                    for (int i7 = 0; i7 < s7; i7++) {
                      for (int i8 = 0; i8 < s8; i8++) {
                        a[i0,i1,i2,i3,i4,i5,i6,i7,i8] = z;
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
      return a;
    }
    public static T[,,,,,,,,,] InitNewArray10<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3, BigInteger size4, BigInteger size5, BigInteger size6, BigInteger size7, BigInteger size8, BigInteger size9) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      int s4 = (int)size4;
      int s5 = (int)size5;
      int s6 = (int)size6;
      int s7 = (int)size7;
      int s8 = (int)size8;
      int s9 = (int)size9;
      T[,,,,,,,,,] a = new T[s0,s1,s2,s3,s4,s5,s6,s7,s8,s9];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              for (int i4 = 0; i4 < s4; i4++) {
                for (int i5 = 0; i5 < s5; i5++) {
                  for (int i6 = 0; i6 < s6; i6++) {
                    for (int i7 = 0; i7 < s7; i7++) {
                      for (int i8 = 0; i8 < s8; i8++) {
                        for (int i9 = 0; i9 < s9; i9++) {
                          a[i0,i1,i2,i3,i4,i5,i6,i7,i8,i9] = z;
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
      return a;
    }
    public static T[,,,,,,,,,,] InitNewArray11<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3, BigInteger size4, BigInteger size5, BigInteger size6, BigInteger size7, BigInteger size8, BigInteger size9, BigInteger size10) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      int s4 = (int)size4;
      int s5 = (int)size5;
      int s6 = (int)size6;
      int s7 = (int)size7;
      int s8 = (int)size8;
      int s9 = (int)size9;
      int s10 = (int)size10;
      T[,,,,,,,,,,] a = new T[s0,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              for (int i4 = 0; i4 < s4; i4++) {
                for (int i5 = 0; i5 < s5; i5++) {
                  for (int i6 = 0; i6 < s6; i6++) {
                    for (int i7 = 0; i7 < s7; i7++) {
                      for (int i8 = 0; i8 < s8; i8++) {
                        for (int i9 = 0; i9 < s9; i9++) {
                          for (int i10 = 0; i10 < s10; i10++) {
                            a[i0,i1,i2,i3,i4,i5,i6,i7,i8,i9,i10] = z;
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
      return a;
    }
    public static T[,,,,,,,,,,,] InitNewArray12<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3, BigInteger size4, BigInteger size5, BigInteger size6, BigInteger size7, BigInteger size8, BigInteger size9, BigInteger size10, BigInteger size11) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      int s4 = (int)size4;
      int s5 = (int)size5;
      int s6 = (int)size6;
      int s7 = (int)size7;
      int s8 = (int)size8;
      int s9 = (int)size9;
      int s10 = (int)size10;
      int s11 = (int)size11;
      T[,,,,,,,,,,,] a = new T[s0,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              for (int i4 = 0; i4 < s4; i4++) {
                for (int i5 = 0; i5 < s5; i5++) {
                  for (int i6 = 0; i6 < s6; i6++) {
                    for (int i7 = 0; i7 < s7; i7++) {
                      for (int i8 = 0; i8 < s8; i8++) {
                        for (int i9 = 0; i9 < s9; i9++) {
                          for (int i10 = 0; i10 < s10; i10++) {
                            for (int i11 = 0; i11 < s11; i11++) {
                              a[i0,i1,i2,i3,i4,i5,i6,i7,i8,i9,i10,i11] = z;
                            }
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
      return a;
    }
    public static T[,,,,,,,,,,,,] InitNewArray13<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3, BigInteger size4, BigInteger size5, BigInteger size6, BigInteger size7, BigInteger size8, BigInteger size9, BigInteger size10, BigInteger size11, BigInteger size12) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      int s4 = (int)size4;
      int s5 = (int)size5;
      int s6 = (int)size6;
      int s7 = (int)size7;
      int s8 = (int)size8;
      int s9 = (int)size9;
      int s10 = (int)size10;
      int s11 = (int)size11;
      int s12 = (int)size12;
      T[,,,,,,,,,,,,] a = new T[s0,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              for (int i4 = 0; i4 < s4; i4++) {
                for (int i5 = 0; i5 < s5; i5++) {
                  for (int i6 = 0; i6 < s6; i6++) {
                    for (int i7 = 0; i7 < s7; i7++) {
                      for (int i8 = 0; i8 < s8; i8++) {
                        for (int i9 = 0; i9 < s9; i9++) {
                          for (int i10 = 0; i10 < s10; i10++) {
                            for (int i11 = 0; i11 < s11; i11++) {
                              for (int i12 = 0; i12 < s12; i12++) {
                                a[i0,i1,i2,i3,i4,i5,i6,i7,i8,i9,i10,i11,i12] = z;
                              }
                            }
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
      return a;
    }
    public static T[,,,,,,,,,,,,,] InitNewArray14<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3, BigInteger size4, BigInteger size5, BigInteger size6, BigInteger size7, BigInteger size8, BigInteger size9, BigInteger size10, BigInteger size11, BigInteger size12, BigInteger size13) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      int s4 = (int)size4;
      int s5 = (int)size5;
      int s6 = (int)size6;
      int s7 = (int)size7;
      int s8 = (int)size8;
      int s9 = (int)size9;
      int s10 = (int)size10;
      int s11 = (int)size11;
      int s12 = (int)size12;
      int s13 = (int)size13;
      T[,,,,,,,,,,,,,] a = new T[s0,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              for (int i4 = 0; i4 < s4; i4++) {
                for (int i5 = 0; i5 < s5; i5++) {
                  for (int i6 = 0; i6 < s6; i6++) {
                    for (int i7 = 0; i7 < s7; i7++) {
                      for (int i8 = 0; i8 < s8; i8++) {
                        for (int i9 = 0; i9 < s9; i9++) {
                          for (int i10 = 0; i10 < s10; i10++) {
                            for (int i11 = 0; i11 < s11; i11++) {
                              for (int i12 = 0; i12 < s12; i12++) {
                                for (int i13 = 0; i13 < s13; i13++) {
                                  a[i0,i1,i2,i3,i4,i5,i6,i7,i8,i9,i10,i11,i12,i13] = z;
                                }
                              }
                            }
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
      return a;
    }
    public static T[,,,,,,,,,,,,,,] InitNewArray15<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3, BigInteger size4, BigInteger size5, BigInteger size6, BigInteger size7, BigInteger size8, BigInteger size9, BigInteger size10, BigInteger size11, BigInteger size12, BigInteger size13, BigInteger size14) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      int s4 = (int)size4;
      int s5 = (int)size5;
      int s6 = (int)size6;
      int s7 = (int)size7;
      int s8 = (int)size8;
      int s9 = (int)size9;
      int s10 = (int)size10;
      int s11 = (int)size11;
      int s12 = (int)size12;
      int s13 = (int)size13;
      int s14 = (int)size14;
      T[,,,,,,,,,,,,,,] a = new T[s0,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              for (int i4 = 0; i4 < s4; i4++) {
                for (int i5 = 0; i5 < s5; i5++) {
                  for (int i6 = 0; i6 < s6; i6++) {
                    for (int i7 = 0; i7 < s7; i7++) {
                      for (int i8 = 0; i8 < s8; i8++) {
                        for (int i9 = 0; i9 < s9; i9++) {
                          for (int i10 = 0; i10 < s10; i10++) {
                            for (int i11 = 0; i11 < s11; i11++) {
                              for (int i12 = 0; i12 < s12; i12++) {
                                for (int i13 = 0; i13 < s13; i13++) {
                                  for (int i14 = 0; i14 < s14; i14++) {
                                    a[i0,i1,i2,i3,i4,i5,i6,i7,i8,i9,i10,i11,i12,i13,i14] = z;
                                  }
                                }
                              }
                            }
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
      return a;
    }
    public static T[,,,,,,,,,,,,,,,] InitNewArray16<T>(T z, BigInteger size0, BigInteger size1, BigInteger size2, BigInteger size3, BigInteger size4, BigInteger size5, BigInteger size6, BigInteger size7, BigInteger size8, BigInteger size9, BigInteger size10, BigInteger size11, BigInteger size12, BigInteger size13, BigInteger size14, BigInteger size15) {
      int s0 = (int)size0;
      int s1 = (int)size1;
      int s2 = (int)size2;
      int s3 = (int)size3;
      int s4 = (int)size4;
      int s5 = (int)size5;
      int s6 = (int)size6;
      int s7 = (int)size7;
      int s8 = (int)size8;
      int s9 = (int)size9;
      int s10 = (int)size10;
      int s11 = (int)size11;
      int s12 = (int)size12;
      int s13 = (int)size13;
      int s14 = (int)size14;
      int s15 = (int)size15;
      T[,,,,,,,,,,,,,,,] a = new T[s0,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15];
      for (int i0 = 0; i0 < s0; i0++) {
        for (int i1 = 0; i1 < s1; i1++) {
          for (int i2 = 0; i2 < s2; i2++) {
            for (int i3 = 0; i3 < s3; i3++) {
              for (int i4 = 0; i4 < s4; i4++) {
                for (int i5 = 0; i5 < s5; i5++) {
                  for (int i6 = 0; i6 < s6; i6++) {
                    for (int i7 = 0; i7 < s7; i7++) {
                      for (int i8 = 0; i8 < s8; i8++) {
                        for (int i9 = 0; i9 < s9; i9++) {
                          for (int i10 = 0; i10 < s10; i10++) {
                            for (int i11 = 0; i11 < s11; i11++) {
                              for (int i12 = 0; i12 < s12; i12++) {
                                for (int i13 = 0; i13 < s13; i13++) {
                                  for (int i14 = 0; i14 < s14; i14++) {
                                    for (int i15 = 0; i15 < s15; i15++) {
                                      a[i0,i1,i2,i3,i4,i5,i6,i7,i8,i9,i10,i11,i12,i13,i14,i15] = z;
                                    }
                                  }
                                }
                              }
                            }
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
      return a;
    }
  }
} // end of namespace Dafny
internal static class FuncExtensions {
  public static Func<U, UResult> DowncastClone<T, TResult, U, UResult>(this Func<T, TResult> F, Func<U, T> ArgConv, Func<TResult, UResult> ResConv) {
    return arg => ResConv(F(ArgConv(arg)));
  }
  public static Func<UResult> DowncastClone<TResult, UResult>(this Func<TResult> F, Func<TResult, UResult> ResConv) {
    return () => ResConv(F());
  }
  public static Func<U1, U2, UResult> DowncastClone<T1, T2, TResult, U1, U2, UResult>(this Func<T1, T2, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<TResult, UResult> ResConv) {
    return (arg1, arg2) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2)));
  }
  public static Func<U1, U2, U3, UResult> DowncastClone<T1, T2, T3, TResult, U1, U2, U3, UResult>(this Func<T1, T2, T3, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3)));
  }
  public static Func<U1, U2, U3, U4, UResult> DowncastClone<T1, T2, T3, T4, TResult, U1, U2, U3, U4, UResult>(this Func<T1, T2, T3, T4, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4)));
  }
  public static Func<U1, U2, U3, U4, U5, UResult> DowncastClone<T1, T2, T3, T4, T5, TResult, U1, U2, U3, U4, U5, UResult>(this Func<T1, T2, T3, T4, T5, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5)));
  }
  public static Func<U1, U2, U3, U4, U5, U6, UResult> DowncastClone<T1, T2, T3, T4, T5, T6, TResult, U1, U2, U3, U4, U5, U6, UResult>(this Func<T1, T2, T3, T4, T5, T6, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<U6, T6> ArgConv6, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5, arg6) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5), ArgConv6(arg6)));
  }
  public static Func<U1, U2, U3, U4, U5, U6, U7, UResult> DowncastClone<T1, T2, T3, T4, T5, T6, T7, TResult, U1, U2, U3, U4, U5, U6, U7, UResult>(this Func<T1, T2, T3, T4, T5, T6, T7, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<U6, T6> ArgConv6, Func<U7, T7> ArgConv7, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5, arg6, arg7) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5), ArgConv6(arg6), ArgConv7(arg7)));
  }
  public static Func<U1, U2, U3, U4, U5, U6, U7, U8, UResult> DowncastClone<T1, T2, T3, T4, T5, T6, T7, T8, TResult, U1, U2, U3, U4, U5, U6, U7, U8, UResult>(this Func<T1, T2, T3, T4, T5, T6, T7, T8, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<U6, T6> ArgConv6, Func<U7, T7> ArgConv7, Func<U8, T8> ArgConv8, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5), ArgConv6(arg6), ArgConv7(arg7), ArgConv8(arg8)));
  }
  public static Func<U1, U2, U3, U4, U5, U6, U7, U8, U9, UResult> DowncastClone<T1, T2, T3, T4, T5, T6, T7, T8, T9, TResult, U1, U2, U3, U4, U5, U6, U7, U8, U9, UResult>(this Func<T1, T2, T3, T4, T5, T6, T7, T8, T9, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<U6, T6> ArgConv6, Func<U7, T7> ArgConv7, Func<U8, T8> ArgConv8, Func<U9, T9> ArgConv9, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5), ArgConv6(arg6), ArgConv7(arg7), ArgConv8(arg8), ArgConv9(arg9)));
  }
  public static Func<U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, UResult> DowncastClone<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, TResult, U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, UResult>(this Func<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<U6, T6> ArgConv6, Func<U7, T7> ArgConv7, Func<U8, T8> ArgConv8, Func<U9, T9> ArgConv9, Func<U10, T10> ArgConv10, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5), ArgConv6(arg6), ArgConv7(arg7), ArgConv8(arg8), ArgConv9(arg9), ArgConv10(arg10)));
  }
  public static Func<U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, UResult> DowncastClone<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, TResult, U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, UResult>(this Func<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<U6, T6> ArgConv6, Func<U7, T7> ArgConv7, Func<U8, T8> ArgConv8, Func<U9, T9> ArgConv9, Func<U10, T10> ArgConv10, Func<U11, T11> ArgConv11, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5), ArgConv6(arg6), ArgConv7(arg7), ArgConv8(arg8), ArgConv9(arg9), ArgConv10(arg10), ArgConv11(arg11)));
  }
  public static Func<U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, U12, UResult> DowncastClone<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, TResult, U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, U12, UResult>(this Func<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<U6, T6> ArgConv6, Func<U7, T7> ArgConv7, Func<U8, T8> ArgConv8, Func<U9, T9> ArgConv9, Func<U10, T10> ArgConv10, Func<U11, T11> ArgConv11, Func<U12, T12> ArgConv12, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11, arg12) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5), ArgConv6(arg6), ArgConv7(arg7), ArgConv8(arg8), ArgConv9(arg9), ArgConv10(arg10), ArgConv11(arg11), ArgConv12(arg12)));
  }
  public static Func<U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, U12, U13, UResult> DowncastClone<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, TResult, U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, U12, U13, UResult>(this Func<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<U6, T6> ArgConv6, Func<U7, T7> ArgConv7, Func<U8, T8> ArgConv8, Func<U9, T9> ArgConv9, Func<U10, T10> ArgConv10, Func<U11, T11> ArgConv11, Func<U12, T12> ArgConv12, Func<U13, T13> ArgConv13, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11, arg12, arg13) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5), ArgConv6(arg6), ArgConv7(arg7), ArgConv8(arg8), ArgConv9(arg9), ArgConv10(arg10), ArgConv11(arg11), ArgConv12(arg12), ArgConv13(arg13)));
  }
  public static Func<U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, U12, U13, U14, UResult> DowncastClone<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, TResult, U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, U12, U13, U14, UResult>(this Func<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<U6, T6> ArgConv6, Func<U7, T7> ArgConv7, Func<U8, T8> ArgConv8, Func<U9, T9> ArgConv9, Func<U10, T10> ArgConv10, Func<U11, T11> ArgConv11, Func<U12, T12> ArgConv12, Func<U13, T13> ArgConv13, Func<U14, T14> ArgConv14, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11, arg12, arg13, arg14) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5), ArgConv6(arg6), ArgConv7(arg7), ArgConv8(arg8), ArgConv9(arg9), ArgConv10(arg10), ArgConv11(arg11), ArgConv12(arg12), ArgConv13(arg13), ArgConv14(arg14)));
  }
  public static Func<U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, U12, U13, U14, U15, UResult> DowncastClone<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, TResult, U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, U12, U13, U14, U15, UResult>(this Func<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<U6, T6> ArgConv6, Func<U7, T7> ArgConv7, Func<U8, T8> ArgConv8, Func<U9, T9> ArgConv9, Func<U10, T10> ArgConv10, Func<U11, T11> ArgConv11, Func<U12, T12> ArgConv12, Func<U13, T13> ArgConv13, Func<U14, T14> ArgConv14, Func<U15, T15> ArgConv15, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11, arg12, arg13, arg14, arg15) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5), ArgConv6(arg6), ArgConv7(arg7), ArgConv8(arg8), ArgConv9(arg9), ArgConv10(arg10), ArgConv11(arg11), ArgConv12(arg12), ArgConv13(arg13), ArgConv14(arg14), ArgConv15(arg15)));
  }
  public static Func<U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, U12, U13, U14, U15, U16, UResult> DowncastClone<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, TResult, U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, U12, U13, U14, U15, U16, UResult>(this Func<T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<U6, T6> ArgConv6, Func<U7, T7> ArgConv7, Func<U8, T8> ArgConv8, Func<U9, T9> ArgConv9, Func<U10, T10> ArgConv10, Func<U11, T11> ArgConv11, Func<U12, T12> ArgConv12, Func<U13, T13> ArgConv13, Func<U14, T14> ArgConv14, Func<U15, T15> ArgConv15, Func<U16, T16> ArgConv16, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11, arg12, arg13, arg14, arg15, arg16) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5), ArgConv6(arg6), ArgConv7(arg7), ArgConv8(arg8), ArgConv9(arg9), ArgConv10(arg10), ArgConv11(arg11), ArgConv12(arg12), ArgConv13(arg13), ArgConv14(arg14), ArgConv15(arg15), ArgConv16(arg16)));
  }
}
// end of class FuncExtensions
#endif
namespace _System {

  public partial class nat {
    private static readonly Dafny.TypeDescriptor<BigInteger> _TYPE = new Dafny.TypeDescriptor<BigInteger>(BigInteger.Zero);
    public static Dafny.TypeDescriptor<BigInteger> _TypeDescriptor() {
      return _TYPE;
    }
    public static bool _Is(BigInteger __source) {
      BigInteger _0_x = __source;
      return (_0_x).Sign != -1;
    }
  }

  public interface _ITuple2<out T0, out T1> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    _ITuple2<__T0, __T1> DowncastClone<__T0, __T1>(Func<T0, __T0> converter0, Func<T1, __T1> converter1);
  }
  public class Tuple2<T0, T1> : _ITuple2<T0, T1> {
    public readonly T0 __0;
    public readonly T1 __1;
    public Tuple2(T0 _0, T1 _1) {
      this.__0 = _0;
      this.__1 = _1;
    }
    public _ITuple2<__T0, __T1> DowncastClone<__T0, __T1>(Func<T0, __T0> converter0, Func<T1, __T1> converter1) {
      if (this is _ITuple2<__T0, __T1> dt) { return dt; }
      return new Tuple2<__T0, __T1>(converter0(__0), converter1(__1));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple2<T0, T1>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ")";
      return s;
    }
    public static _System._ITuple2<T0, T1> Default(T0 _default_T0, T1 _default_T1) {
      return create(_default_T0, _default_T1);
    }
    public static Dafny.TypeDescriptor<_System._ITuple2<T0, T1>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1) {
      return new Dafny.TypeDescriptor<_System._ITuple2<T0, T1>>(_System.Tuple2<T0, T1>.Default(_td_T0.Default(), _td_T1.Default()));
    }
    public static _ITuple2<T0, T1> create(T0 _0, T1 _1) {
      return new Tuple2<T0, T1>(_0, _1);
    }
    public static _ITuple2<T0, T1> create____hMake2(T0 _0, T1 _1) {
      return create(_0, _1);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
  }

  public interface _ITuple0 {
    _ITuple0 DowncastClone();
  }
  public class Tuple0 : _ITuple0 {
    public Tuple0() {
    }
    public _ITuple0 DowncastClone() {
      if (this is _ITuple0 dt) { return dt; }
      return new Tuple0();
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple0;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      return "()";
    }
    private static readonly _System._ITuple0 theDefault = create();
    public static _System._ITuple0 Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<_System._ITuple0> _TYPE = new Dafny.TypeDescriptor<_System._ITuple0>(_System.Tuple0.Default());
    public static Dafny.TypeDescriptor<_System._ITuple0> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ITuple0 create() {
      return new Tuple0();
    }
    public static _ITuple0 create____hMake0() {
      return create();
    }
    public static System.Collections.Generic.IEnumerable<_ITuple0> AllSingletonConstructors {
      get {
        yield return Tuple0.create();
      }
    }
  }

  public interface _ITuple1<out T0> {
    T0 dtor__0 { get; }
    _ITuple1<__T0> DowncastClone<__T0>(Func<T0, __T0> converter0);
  }
  public class Tuple1<T0> : _ITuple1<T0> {
    public readonly T0 __0;
    public Tuple1(T0 _0) {
      this.__0 = _0;
    }
    public _ITuple1<__T0> DowncastClone<__T0>(Func<T0, __T0> converter0) {
      if (this is _ITuple1<__T0> dt) { return dt; }
      return new Tuple1<__T0>(converter0(__0));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple1<T0>;
      return oth != null && object.Equals(this.__0, oth.__0);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ")";
      return s;
    }
    public static _System._ITuple1<T0> Default(T0 _default_T0) {
      return create(_default_T0);
    }
    public static Dafny.TypeDescriptor<_System._ITuple1<T0>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0) {
      return new Dafny.TypeDescriptor<_System._ITuple1<T0>>(_System.Tuple1<T0>.Default(_td_T0.Default()));
    }
    public static _ITuple1<T0> create(T0 _0) {
      return new Tuple1<T0>(_0);
    }
    public static _ITuple1<T0> create____hMake1(T0 _0) {
      return create(_0);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
  }

  public interface _ITuple3<out T0, out T1, out T2> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    _ITuple3<__T0, __T1, __T2> DowncastClone<__T0, __T1, __T2>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2);
  }
  public class Tuple3<T0, T1, T2> : _ITuple3<T0, T1, T2> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public Tuple3(T0 _0, T1 _1, T2 _2) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
    }
    public _ITuple3<__T0, __T1, __T2> DowncastClone<__T0, __T1, __T2>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2) {
      if (this is _ITuple3<__T0, __T1, __T2> dt) { return dt; }
      return new Tuple3<__T0, __T1, __T2>(converter0(__0), converter1(__1), converter2(__2));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple3<T0, T1, T2>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ")";
      return s;
    }
    public static _System._ITuple3<T0, T1, T2> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2) {
      return create(_default_T0, _default_T1, _default_T2);
    }
    public static Dafny.TypeDescriptor<_System._ITuple3<T0, T1, T2>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2) {
      return new Dafny.TypeDescriptor<_System._ITuple3<T0, T1, T2>>(_System.Tuple3<T0, T1, T2>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default()));
    }
    public static _ITuple3<T0, T1, T2> create(T0 _0, T1 _1, T2 _2) {
      return new Tuple3<T0, T1, T2>(_0, _1, _2);
    }
    public static _ITuple3<T0, T1, T2> create____hMake3(T0 _0, T1 _1, T2 _2) {
      return create(_0, _1, _2);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
  }

  public interface _ITuple4<out T0, out T1, out T2, out T3> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    _ITuple4<__T0, __T1, __T2, __T3> DowncastClone<__T0, __T1, __T2, __T3>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3);
  }
  public class Tuple4<T0, T1, T2, T3> : _ITuple4<T0, T1, T2, T3> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public Tuple4(T0 _0, T1 _1, T2 _2, T3 _3) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
    }
    public _ITuple4<__T0, __T1, __T2, __T3> DowncastClone<__T0, __T1, __T2, __T3>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3) {
      if (this is _ITuple4<__T0, __T1, __T2, __T3> dt) { return dt; }
      return new Tuple4<__T0, __T1, __T2, __T3>(converter0(__0), converter1(__1), converter2(__2), converter3(__3));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple4<T0, T1, T2, T3>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ")";
      return s;
    }
    public static _System._ITuple4<T0, T1, T2, T3> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3);
    }
    public static Dafny.TypeDescriptor<_System._ITuple4<T0, T1, T2, T3>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3) {
      return new Dafny.TypeDescriptor<_System._ITuple4<T0, T1, T2, T3>>(_System.Tuple4<T0, T1, T2, T3>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default()));
    }
    public static _ITuple4<T0, T1, T2, T3> create(T0 _0, T1 _1, T2 _2, T3 _3) {
      return new Tuple4<T0, T1, T2, T3>(_0, _1, _2, _3);
    }
    public static _ITuple4<T0, T1, T2, T3> create____hMake4(T0 _0, T1 _1, T2 _2, T3 _3) {
      return create(_0, _1, _2, _3);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
  }

  public interface _ITuple5<out T0, out T1, out T2, out T3, out T4> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    _ITuple5<__T0, __T1, __T2, __T3, __T4> DowncastClone<__T0, __T1, __T2, __T3, __T4>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4);
  }
  public class Tuple5<T0, T1, T2, T3, T4> : _ITuple5<T0, T1, T2, T3, T4> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public Tuple5(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
    }
    public _ITuple5<__T0, __T1, __T2, __T3, __T4> DowncastClone<__T0, __T1, __T2, __T3, __T4>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4) {
      if (this is _ITuple5<__T0, __T1, __T2, __T3, __T4> dt) { return dt; }
      return new Tuple5<__T0, __T1, __T2, __T3, __T4>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple5<T0, T1, T2, T3, T4>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ")";
      return s;
    }
    public static _System._ITuple5<T0, T1, T2, T3, T4> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4);
    }
    public static Dafny.TypeDescriptor<_System._ITuple5<T0, T1, T2, T3, T4>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4) {
      return new Dafny.TypeDescriptor<_System._ITuple5<T0, T1, T2, T3, T4>>(_System.Tuple5<T0, T1, T2, T3, T4>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default()));
    }
    public static _ITuple5<T0, T1, T2, T3, T4> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4) {
      return new Tuple5<T0, T1, T2, T3, T4>(_0, _1, _2, _3, _4);
    }
    public static _ITuple5<T0, T1, T2, T3, T4> create____hMake5(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4) {
      return create(_0, _1, _2, _3, _4);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
  }

  public interface _ITuple6<out T0, out T1, out T2, out T3, out T4, out T5> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    _ITuple6<__T0, __T1, __T2, __T3, __T4, __T5> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5);
  }
  public class Tuple6<T0, T1, T2, T3, T4, T5> : _ITuple6<T0, T1, T2, T3, T4, T5> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public Tuple6(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
    }
    public _ITuple6<__T0, __T1, __T2, __T3, __T4, __T5> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5) {
      if (this is _ITuple6<__T0, __T1, __T2, __T3, __T4, __T5> dt) { return dt; }
      return new Tuple6<__T0, __T1, __T2, __T3, __T4, __T5>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple6<T0, T1, T2, T3, T4, T5>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ")";
      return s;
    }
    public static _System._ITuple6<T0, T1, T2, T3, T4, T5> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5);
    }
    public static Dafny.TypeDescriptor<_System._ITuple6<T0, T1, T2, T3, T4, T5>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5) {
      return new Dafny.TypeDescriptor<_System._ITuple6<T0, T1, T2, T3, T4, T5>>(_System.Tuple6<T0, T1, T2, T3, T4, T5>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default()));
    }
    public static _ITuple6<T0, T1, T2, T3, T4, T5> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5) {
      return new Tuple6<T0, T1, T2, T3, T4, T5>(_0, _1, _2, _3, _4, _5);
    }
    public static _ITuple6<T0, T1, T2, T3, T4, T5> create____hMake6(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5) {
      return create(_0, _1, _2, _3, _4, _5);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
  }

  public interface _ITuple7<out T0, out T1, out T2, out T3, out T4, out T5, out T6> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    _ITuple7<__T0, __T1, __T2, __T3, __T4, __T5, __T6> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6);
  }
  public class Tuple7<T0, T1, T2, T3, T4, T5, T6> : _ITuple7<T0, T1, T2, T3, T4, T5, T6> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public Tuple7(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
    }
    public _ITuple7<__T0, __T1, __T2, __T3, __T4, __T5, __T6> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6) {
      if (this is _ITuple7<__T0, __T1, __T2, __T3, __T4, __T5, __T6> dt) { return dt; }
      return new Tuple7<__T0, __T1, __T2, __T3, __T4, __T5, __T6>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple7<T0, T1, T2, T3, T4, T5, T6>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ")";
      return s;
    }
    public static _System._ITuple7<T0, T1, T2, T3, T4, T5, T6> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6);
    }
    public static Dafny.TypeDescriptor<_System._ITuple7<T0, T1, T2, T3, T4, T5, T6>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6) {
      return new Dafny.TypeDescriptor<_System._ITuple7<T0, T1, T2, T3, T4, T5, T6>>(_System.Tuple7<T0, T1, T2, T3, T4, T5, T6>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default()));
    }
    public static _ITuple7<T0, T1, T2, T3, T4, T5, T6> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6) {
      return new Tuple7<T0, T1, T2, T3, T4, T5, T6>(_0, _1, _2, _3, _4, _5, _6);
    }
    public static _ITuple7<T0, T1, T2, T3, T4, T5, T6> create____hMake7(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6) {
      return create(_0, _1, _2, _3, _4, _5, _6);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
  }

  public interface _ITuple8<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    _ITuple8<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7);
  }
  public class Tuple8<T0, T1, T2, T3, T4, T5, T6, T7> : _ITuple8<T0, T1, T2, T3, T4, T5, T6, T7> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public Tuple8(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
    }
    public _ITuple8<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7) {
      if (this is _ITuple8<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7> dt) { return dt; }
      return new Tuple8<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple8<T0, T1, T2, T3, T4, T5, T6, T7>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ")";
      return s;
    }
    public static _System._ITuple8<T0, T1, T2, T3, T4, T5, T6, T7> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7);
    }
    public static Dafny.TypeDescriptor<_System._ITuple8<T0, T1, T2, T3, T4, T5, T6, T7>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7) {
      return new Dafny.TypeDescriptor<_System._ITuple8<T0, T1, T2, T3, T4, T5, T6, T7>>(_System.Tuple8<T0, T1, T2, T3, T4, T5, T6, T7>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default()));
    }
    public static _ITuple8<T0, T1, T2, T3, T4, T5, T6, T7> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7) {
      return new Tuple8<T0, T1, T2, T3, T4, T5, T6, T7>(_0, _1, _2, _3, _4, _5, _6, _7);
    }
    public static _ITuple8<T0, T1, T2, T3, T4, T5, T6, T7> create____hMake8(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
  }

  public interface _ITuple9<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    _ITuple9<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8);
  }
  public class Tuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8> : _ITuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public readonly T8 __8;
    public Tuple9(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
      this.__8 = _8;
    }
    public _ITuple9<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8) {
      if (this is _ITuple9<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8> dt) { return dt; }
      return new Tuple9<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7), converter8(__8));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7) && object.Equals(this.__8, oth.__8);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__8));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__8);
      s += ")";
      return s;
    }
    public static _System._ITuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8);
    }
    public static Dafny.TypeDescriptor<_System._ITuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8) {
      return new Dafny.TypeDescriptor<_System._ITuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8>>(_System.Tuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default()));
    }
    public static _ITuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8) {
      return new Tuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8>(_0, _1, _2, _3, _4, _5, _6, _7, _8);
    }
    public static _ITuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8> create____hMake9(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7, _8);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
    public T8 dtor__8 {
      get {
        return this.__8;
      }
    }
  }

  public interface _ITuple10<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    _ITuple10<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9);
  }
  public class Tuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9> : _ITuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public readonly T8 __8;
    public readonly T9 __9;
    public Tuple10(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
      this.__8 = _8;
      this.__9 = _9;
    }
    public _ITuple10<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9) {
      if (this is _ITuple10<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9> dt) { return dt; }
      return new Tuple10<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7), converter8(__8), converter9(__9));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7) && object.Equals(this.__8, oth.__8) && object.Equals(this.__9, oth.__9);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__9));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__8);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__9);
      s += ")";
      return s;
    }
    public static _System._ITuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9);
    }
    public static Dafny.TypeDescriptor<_System._ITuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9) {
      return new Dafny.TypeDescriptor<_System._ITuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9>>(_System.Tuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default()));
    }
    public static _ITuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9) {
      return new Tuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9);
    }
    public static _ITuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9> create____hMake10(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
    public T8 dtor__8 {
      get {
        return this.__8;
      }
    }
    public T9 dtor__9 {
      get {
        return this.__9;
      }
    }
  }

  public interface _ITuple11<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    _ITuple11<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10);
  }
  public class Tuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10> : _ITuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public readonly T8 __8;
    public readonly T9 __9;
    public readonly T10 __10;
    public Tuple11(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
      this.__8 = _8;
      this.__9 = _9;
      this.__10 = _10;
    }
    public _ITuple11<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10) {
      if (this is _ITuple11<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10> dt) { return dt; }
      return new Tuple11<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7), converter8(__8), converter9(__9), converter10(__10));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7) && object.Equals(this.__8, oth.__8) && object.Equals(this.__9, oth.__9) && object.Equals(this.__10, oth.__10);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__10));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__8);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__9);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__10);
      s += ")";
      return s;
    }
    public static _System._ITuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10);
    }
    public static Dafny.TypeDescriptor<_System._ITuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10) {
      return new Dafny.TypeDescriptor<_System._ITuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10>>(_System.Tuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default()));
    }
    public static _ITuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10) {
      return new Tuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10);
    }
    public static _ITuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10> create____hMake11(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
    public T8 dtor__8 {
      get {
        return this.__8;
      }
    }
    public T9 dtor__9 {
      get {
        return this.__9;
      }
    }
    public T10 dtor__10 {
      get {
        return this.__10;
      }
    }
  }

  public interface _ITuple12<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    _ITuple12<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11);
  }
  public class Tuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11> : _ITuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public readonly T8 __8;
    public readonly T9 __9;
    public readonly T10 __10;
    public readonly T11 __11;
    public Tuple12(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
      this.__8 = _8;
      this.__9 = _9;
      this.__10 = _10;
      this.__11 = _11;
    }
    public _ITuple12<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11) {
      if (this is _ITuple12<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11> dt) { return dt; }
      return new Tuple12<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7), converter8(__8), converter9(__9), converter10(__10), converter11(__11));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7) && object.Equals(this.__8, oth.__8) && object.Equals(this.__9, oth.__9) && object.Equals(this.__10, oth.__10) && object.Equals(this.__11, oth.__11);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__11));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__8);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__9);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__10);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__11);
      s += ")";
      return s;
    }
    public static _System._ITuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11);
    }
    public static Dafny.TypeDescriptor<_System._ITuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11) {
      return new Dafny.TypeDescriptor<_System._ITuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11>>(_System.Tuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default()));
    }
    public static _ITuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11) {
      return new Tuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11);
    }
    public static _ITuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11> create____hMake12(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
    public T8 dtor__8 {
      get {
        return this.__8;
      }
    }
    public T9 dtor__9 {
      get {
        return this.__9;
      }
    }
    public T10 dtor__10 {
      get {
        return this.__10;
      }
    }
    public T11 dtor__11 {
      get {
        return this.__11;
      }
    }
  }

  public interface _ITuple13<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11, out T12> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    T12 dtor__12 { get; }
    _ITuple13<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12);
  }
  public class Tuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12> : _ITuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public readonly T8 __8;
    public readonly T9 __9;
    public readonly T10 __10;
    public readonly T11 __11;
    public readonly T12 __12;
    public Tuple13(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
      this.__8 = _8;
      this.__9 = _9;
      this.__10 = _10;
      this.__11 = _11;
      this.__12 = _12;
    }
    public _ITuple13<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12) {
      if (this is _ITuple13<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12> dt) { return dt; }
      return new Tuple13<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7), converter8(__8), converter9(__9), converter10(__10), converter11(__11), converter12(__12));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7) && object.Equals(this.__8, oth.__8) && object.Equals(this.__9, oth.__9) && object.Equals(this.__10, oth.__10) && object.Equals(this.__11, oth.__11) && object.Equals(this.__12, oth.__12);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__11));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__12));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__8);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__9);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__10);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__11);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__12);
      s += ")";
      return s;
    }
    public static _System._ITuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11, T12 _default_T12) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11, _default_T12);
    }
    public static Dafny.TypeDescriptor<_System._ITuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11, Dafny.TypeDescriptor<T12> _td_T12) {
      return new Dafny.TypeDescriptor<_System._ITuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12>>(_System.Tuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default(), _td_T12.Default()));
    }
    public static _ITuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12) {
      return new Tuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12);
    }
    public static _ITuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12> create____hMake13(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
    public T8 dtor__8 {
      get {
        return this.__8;
      }
    }
    public T9 dtor__9 {
      get {
        return this.__9;
      }
    }
    public T10 dtor__10 {
      get {
        return this.__10;
      }
    }
    public T11 dtor__11 {
      get {
        return this.__11;
      }
    }
    public T12 dtor__12 {
      get {
        return this.__12;
      }
    }
  }

  public interface _ITuple14<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11, out T12, out T13> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    T12 dtor__12 { get; }
    T13 dtor__13 { get; }
    _ITuple14<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13);
  }
  public class Tuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13> : _ITuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public readonly T8 __8;
    public readonly T9 __9;
    public readonly T10 __10;
    public readonly T11 __11;
    public readonly T12 __12;
    public readonly T13 __13;
    public Tuple14(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
      this.__8 = _8;
      this.__9 = _9;
      this.__10 = _10;
      this.__11 = _11;
      this.__12 = _12;
      this.__13 = _13;
    }
    public _ITuple14<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13) {
      if (this is _ITuple14<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13> dt) { return dt; }
      return new Tuple14<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7), converter8(__8), converter9(__9), converter10(__10), converter11(__11), converter12(__12), converter13(__13));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7) && object.Equals(this.__8, oth.__8) && object.Equals(this.__9, oth.__9) && object.Equals(this.__10, oth.__10) && object.Equals(this.__11, oth.__11) && object.Equals(this.__12, oth.__12) && object.Equals(this.__13, oth.__13);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__11));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__12));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__13));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__8);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__9);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__10);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__11);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__12);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__13);
      s += ")";
      return s;
    }
    public static _System._ITuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11, T12 _default_T12, T13 _default_T13) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11, _default_T12, _default_T13);
    }
    public static Dafny.TypeDescriptor<_System._ITuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11, Dafny.TypeDescriptor<T12> _td_T12, Dafny.TypeDescriptor<T13> _td_T13) {
      return new Dafny.TypeDescriptor<_System._ITuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13>>(_System.Tuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default(), _td_T12.Default(), _td_T13.Default()));
    }
    public static _ITuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13) {
      return new Tuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13);
    }
    public static _ITuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13> create____hMake14(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
    public T8 dtor__8 {
      get {
        return this.__8;
      }
    }
    public T9 dtor__9 {
      get {
        return this.__9;
      }
    }
    public T10 dtor__10 {
      get {
        return this.__10;
      }
    }
    public T11 dtor__11 {
      get {
        return this.__11;
      }
    }
    public T12 dtor__12 {
      get {
        return this.__12;
      }
    }
    public T13 dtor__13 {
      get {
        return this.__13;
      }
    }
  }

  public interface _ITuple15<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11, out T12, out T13, out T14> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    T12 dtor__12 { get; }
    T13 dtor__13 { get; }
    T14 dtor__14 { get; }
    _ITuple15<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14);
  }
  public class Tuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14> : _ITuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public readonly T8 __8;
    public readonly T9 __9;
    public readonly T10 __10;
    public readonly T11 __11;
    public readonly T12 __12;
    public readonly T13 __13;
    public readonly T14 __14;
    public Tuple15(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
      this.__8 = _8;
      this.__9 = _9;
      this.__10 = _10;
      this.__11 = _11;
      this.__12 = _12;
      this.__13 = _13;
      this.__14 = _14;
    }
    public _ITuple15<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14) {
      if (this is _ITuple15<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14> dt) { return dt; }
      return new Tuple15<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7), converter8(__8), converter9(__9), converter10(__10), converter11(__11), converter12(__12), converter13(__13), converter14(__14));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7) && object.Equals(this.__8, oth.__8) && object.Equals(this.__9, oth.__9) && object.Equals(this.__10, oth.__10) && object.Equals(this.__11, oth.__11) && object.Equals(this.__12, oth.__12) && object.Equals(this.__13, oth.__13) && object.Equals(this.__14, oth.__14);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__11));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__12));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__13));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__14));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__8);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__9);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__10);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__11);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__12);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__13);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__14);
      s += ")";
      return s;
    }
    public static _System._ITuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11, T12 _default_T12, T13 _default_T13, T14 _default_T14) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11, _default_T12, _default_T13, _default_T14);
    }
    public static Dafny.TypeDescriptor<_System._ITuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11, Dafny.TypeDescriptor<T12> _td_T12, Dafny.TypeDescriptor<T13> _td_T13, Dafny.TypeDescriptor<T14> _td_T14) {
      return new Dafny.TypeDescriptor<_System._ITuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14>>(_System.Tuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default(), _td_T12.Default(), _td_T13.Default(), _td_T14.Default()));
    }
    public static _ITuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14) {
      return new Tuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14);
    }
    public static _ITuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14> create____hMake15(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
    public T8 dtor__8 {
      get {
        return this.__8;
      }
    }
    public T9 dtor__9 {
      get {
        return this.__9;
      }
    }
    public T10 dtor__10 {
      get {
        return this.__10;
      }
    }
    public T11 dtor__11 {
      get {
        return this.__11;
      }
    }
    public T12 dtor__12 {
      get {
        return this.__12;
      }
    }
    public T13 dtor__13 {
      get {
        return this.__13;
      }
    }
    public T14 dtor__14 {
      get {
        return this.__14;
      }
    }
  }

  public interface _ITuple16<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11, out T12, out T13, out T14, out T15> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    T12 dtor__12 { get; }
    T13 dtor__13 { get; }
    T14 dtor__14 { get; }
    T15 dtor__15 { get; }
    _ITuple16<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15);
  }
  public class Tuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15> : _ITuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public readonly T8 __8;
    public readonly T9 __9;
    public readonly T10 __10;
    public readonly T11 __11;
    public readonly T12 __12;
    public readonly T13 __13;
    public readonly T14 __14;
    public readonly T15 __15;
    public Tuple16(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
      this.__8 = _8;
      this.__9 = _9;
      this.__10 = _10;
      this.__11 = _11;
      this.__12 = _12;
      this.__13 = _13;
      this.__14 = _14;
      this.__15 = _15;
    }
    public _ITuple16<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15) {
      if (this is _ITuple16<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15> dt) { return dt; }
      return new Tuple16<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7), converter8(__8), converter9(__9), converter10(__10), converter11(__11), converter12(__12), converter13(__13), converter14(__14), converter15(__15));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7) && object.Equals(this.__8, oth.__8) && object.Equals(this.__9, oth.__9) && object.Equals(this.__10, oth.__10) && object.Equals(this.__11, oth.__11) && object.Equals(this.__12, oth.__12) && object.Equals(this.__13, oth.__13) && object.Equals(this.__14, oth.__14) && object.Equals(this.__15, oth.__15);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__11));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__12));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__13));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__14));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__15));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__8);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__9);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__10);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__11);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__12);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__13);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__14);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__15);
      s += ")";
      return s;
    }
    public static _System._ITuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11, T12 _default_T12, T13 _default_T13, T14 _default_T14, T15 _default_T15) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11, _default_T12, _default_T13, _default_T14, _default_T15);
    }
    public static Dafny.TypeDescriptor<_System._ITuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11, Dafny.TypeDescriptor<T12> _td_T12, Dafny.TypeDescriptor<T13> _td_T13, Dafny.TypeDescriptor<T14> _td_T14, Dafny.TypeDescriptor<T15> _td_T15) {
      return new Dafny.TypeDescriptor<_System._ITuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15>>(_System.Tuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default(), _td_T12.Default(), _td_T13.Default(), _td_T14.Default(), _td_T15.Default()));
    }
    public static _ITuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15) {
      return new Tuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15);
    }
    public static _ITuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15> create____hMake16(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
    public T8 dtor__8 {
      get {
        return this.__8;
      }
    }
    public T9 dtor__9 {
      get {
        return this.__9;
      }
    }
    public T10 dtor__10 {
      get {
        return this.__10;
      }
    }
    public T11 dtor__11 {
      get {
        return this.__11;
      }
    }
    public T12 dtor__12 {
      get {
        return this.__12;
      }
    }
    public T13 dtor__13 {
      get {
        return this.__13;
      }
    }
    public T14 dtor__14 {
      get {
        return this.__14;
      }
    }
    public T15 dtor__15 {
      get {
        return this.__15;
      }
    }
  }

  public interface _ITuple17<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11, out T12, out T13, out T14, out T15, out T16> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    T12 dtor__12 { get; }
    T13 dtor__13 { get; }
    T14 dtor__14 { get; }
    T15 dtor__15 { get; }
    T16 dtor__16 { get; }
    _ITuple17<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15, Func<T16, __T16> converter16);
  }
  public class Tuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16> : _ITuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public readonly T8 __8;
    public readonly T9 __9;
    public readonly T10 __10;
    public readonly T11 __11;
    public readonly T12 __12;
    public readonly T13 __13;
    public readonly T14 __14;
    public readonly T15 __15;
    public readonly T16 __16;
    public Tuple17(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
      this.__8 = _8;
      this.__9 = _9;
      this.__10 = _10;
      this.__11 = _11;
      this.__12 = _12;
      this.__13 = _13;
      this.__14 = _14;
      this.__15 = _15;
      this.__16 = _16;
    }
    public _ITuple17<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15, Func<T16, __T16> converter16) {
      if (this is _ITuple17<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16> dt) { return dt; }
      return new Tuple17<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7), converter8(__8), converter9(__9), converter10(__10), converter11(__11), converter12(__12), converter13(__13), converter14(__14), converter15(__15), converter16(__16));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7) && object.Equals(this.__8, oth.__8) && object.Equals(this.__9, oth.__9) && object.Equals(this.__10, oth.__10) && object.Equals(this.__11, oth.__11) && object.Equals(this.__12, oth.__12) && object.Equals(this.__13, oth.__13) && object.Equals(this.__14, oth.__14) && object.Equals(this.__15, oth.__15) && object.Equals(this.__16, oth.__16);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__11));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__12));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__13));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__14));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__15));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__16));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__8);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__9);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__10);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__11);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__12);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__13);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__14);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__15);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__16);
      s += ")";
      return s;
    }
    public static _System._ITuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11, T12 _default_T12, T13 _default_T13, T14 _default_T14, T15 _default_T15, T16 _default_T16) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11, _default_T12, _default_T13, _default_T14, _default_T15, _default_T16);
    }
    public static Dafny.TypeDescriptor<_System._ITuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11, Dafny.TypeDescriptor<T12> _td_T12, Dafny.TypeDescriptor<T13> _td_T13, Dafny.TypeDescriptor<T14> _td_T14, Dafny.TypeDescriptor<T15> _td_T15, Dafny.TypeDescriptor<T16> _td_T16) {
      return new Dafny.TypeDescriptor<_System._ITuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16>>(_System.Tuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default(), _td_T12.Default(), _td_T13.Default(), _td_T14.Default(), _td_T15.Default(), _td_T16.Default()));
    }
    public static _ITuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16) {
      return new Tuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16);
    }
    public static _ITuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16> create____hMake17(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
    public T8 dtor__8 {
      get {
        return this.__8;
      }
    }
    public T9 dtor__9 {
      get {
        return this.__9;
      }
    }
    public T10 dtor__10 {
      get {
        return this.__10;
      }
    }
    public T11 dtor__11 {
      get {
        return this.__11;
      }
    }
    public T12 dtor__12 {
      get {
        return this.__12;
      }
    }
    public T13 dtor__13 {
      get {
        return this.__13;
      }
    }
    public T14 dtor__14 {
      get {
        return this.__14;
      }
    }
    public T15 dtor__15 {
      get {
        return this.__15;
      }
    }
    public T16 dtor__16 {
      get {
        return this.__16;
      }
    }
  }

  public interface _ITuple18<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11, out T12, out T13, out T14, out T15, out T16, out T17> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    T12 dtor__12 { get; }
    T13 dtor__13 { get; }
    T14 dtor__14 { get; }
    T15 dtor__15 { get; }
    T16 dtor__16 { get; }
    T17 dtor__17 { get; }
    _ITuple18<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15, Func<T16, __T16> converter16, Func<T17, __T17> converter17);
  }
  public class Tuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17> : _ITuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public readonly T8 __8;
    public readonly T9 __9;
    public readonly T10 __10;
    public readonly T11 __11;
    public readonly T12 __12;
    public readonly T13 __13;
    public readonly T14 __14;
    public readonly T15 __15;
    public readonly T16 __16;
    public readonly T17 __17;
    public Tuple18(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16, T17 _17) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
      this.__8 = _8;
      this.__9 = _9;
      this.__10 = _10;
      this.__11 = _11;
      this.__12 = _12;
      this.__13 = _13;
      this.__14 = _14;
      this.__15 = _15;
      this.__16 = _16;
      this.__17 = _17;
    }
    public _ITuple18<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15, Func<T16, __T16> converter16, Func<T17, __T17> converter17) {
      if (this is _ITuple18<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17> dt) { return dt; }
      return new Tuple18<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7), converter8(__8), converter9(__9), converter10(__10), converter11(__11), converter12(__12), converter13(__13), converter14(__14), converter15(__15), converter16(__16), converter17(__17));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7) && object.Equals(this.__8, oth.__8) && object.Equals(this.__9, oth.__9) && object.Equals(this.__10, oth.__10) && object.Equals(this.__11, oth.__11) && object.Equals(this.__12, oth.__12) && object.Equals(this.__13, oth.__13) && object.Equals(this.__14, oth.__14) && object.Equals(this.__15, oth.__15) && object.Equals(this.__16, oth.__16) && object.Equals(this.__17, oth.__17);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__11));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__12));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__13));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__14));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__15));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__16));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__17));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__8);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__9);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__10);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__11);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__12);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__13);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__14);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__15);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__16);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__17);
      s += ")";
      return s;
    }
    public static _System._ITuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11, T12 _default_T12, T13 _default_T13, T14 _default_T14, T15 _default_T15, T16 _default_T16, T17 _default_T17) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11, _default_T12, _default_T13, _default_T14, _default_T15, _default_T16, _default_T17);
    }
    public static Dafny.TypeDescriptor<_System._ITuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11, Dafny.TypeDescriptor<T12> _td_T12, Dafny.TypeDescriptor<T13> _td_T13, Dafny.TypeDescriptor<T14> _td_T14, Dafny.TypeDescriptor<T15> _td_T15, Dafny.TypeDescriptor<T16> _td_T16, Dafny.TypeDescriptor<T17> _td_T17) {
      return new Dafny.TypeDescriptor<_System._ITuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17>>(_System.Tuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default(), _td_T12.Default(), _td_T13.Default(), _td_T14.Default(), _td_T15.Default(), _td_T16.Default(), _td_T17.Default()));
    }
    public static _ITuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16, T17 _17) {
      return new Tuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17);
    }
    public static _ITuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17> create____hMake18(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16, T17 _17) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
    public T8 dtor__8 {
      get {
        return this.__8;
      }
    }
    public T9 dtor__9 {
      get {
        return this.__9;
      }
    }
    public T10 dtor__10 {
      get {
        return this.__10;
      }
    }
    public T11 dtor__11 {
      get {
        return this.__11;
      }
    }
    public T12 dtor__12 {
      get {
        return this.__12;
      }
    }
    public T13 dtor__13 {
      get {
        return this.__13;
      }
    }
    public T14 dtor__14 {
      get {
        return this.__14;
      }
    }
    public T15 dtor__15 {
      get {
        return this.__15;
      }
    }
    public T16 dtor__16 {
      get {
        return this.__16;
      }
    }
    public T17 dtor__17 {
      get {
        return this.__17;
      }
    }
  }

  public interface _ITuple19<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11, out T12, out T13, out T14, out T15, out T16, out T17, out T18> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    T12 dtor__12 { get; }
    T13 dtor__13 { get; }
    T14 dtor__14 { get; }
    T15 dtor__15 { get; }
    T16 dtor__16 { get; }
    T17 dtor__17 { get; }
    T18 dtor__18 { get; }
    _ITuple19<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15, Func<T16, __T16> converter16, Func<T17, __T17> converter17, Func<T18, __T18> converter18);
  }
  public class Tuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18> : _ITuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public readonly T8 __8;
    public readonly T9 __9;
    public readonly T10 __10;
    public readonly T11 __11;
    public readonly T12 __12;
    public readonly T13 __13;
    public readonly T14 __14;
    public readonly T15 __15;
    public readonly T16 __16;
    public readonly T17 __17;
    public readonly T18 __18;
    public Tuple19(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16, T17 _17, T18 _18) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
      this.__8 = _8;
      this.__9 = _9;
      this.__10 = _10;
      this.__11 = _11;
      this.__12 = _12;
      this.__13 = _13;
      this.__14 = _14;
      this.__15 = _15;
      this.__16 = _16;
      this.__17 = _17;
      this.__18 = _18;
    }
    public _ITuple19<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15, Func<T16, __T16> converter16, Func<T17, __T17> converter17, Func<T18, __T18> converter18) {
      if (this is _ITuple19<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18> dt) { return dt; }
      return new Tuple19<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7), converter8(__8), converter9(__9), converter10(__10), converter11(__11), converter12(__12), converter13(__13), converter14(__14), converter15(__15), converter16(__16), converter17(__17), converter18(__18));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7) && object.Equals(this.__8, oth.__8) && object.Equals(this.__9, oth.__9) && object.Equals(this.__10, oth.__10) && object.Equals(this.__11, oth.__11) && object.Equals(this.__12, oth.__12) && object.Equals(this.__13, oth.__13) && object.Equals(this.__14, oth.__14) && object.Equals(this.__15, oth.__15) && object.Equals(this.__16, oth.__16) && object.Equals(this.__17, oth.__17) && object.Equals(this.__18, oth.__18);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__11));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__12));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__13));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__14));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__15));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__16));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__17));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__18));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__8);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__9);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__10);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__11);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__12);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__13);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__14);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__15);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__16);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__17);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__18);
      s += ")";
      return s;
    }
    public static _System._ITuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11, T12 _default_T12, T13 _default_T13, T14 _default_T14, T15 _default_T15, T16 _default_T16, T17 _default_T17, T18 _default_T18) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11, _default_T12, _default_T13, _default_T14, _default_T15, _default_T16, _default_T17, _default_T18);
    }
    public static Dafny.TypeDescriptor<_System._ITuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11, Dafny.TypeDescriptor<T12> _td_T12, Dafny.TypeDescriptor<T13> _td_T13, Dafny.TypeDescriptor<T14> _td_T14, Dafny.TypeDescriptor<T15> _td_T15, Dafny.TypeDescriptor<T16> _td_T16, Dafny.TypeDescriptor<T17> _td_T17, Dafny.TypeDescriptor<T18> _td_T18) {
      return new Dafny.TypeDescriptor<_System._ITuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18>>(_System.Tuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default(), _td_T12.Default(), _td_T13.Default(), _td_T14.Default(), _td_T15.Default(), _td_T16.Default(), _td_T17.Default(), _td_T18.Default()));
    }
    public static _ITuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16, T17 _17, T18 _18) {
      return new Tuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18);
    }
    public static _ITuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18> create____hMake19(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16, T17 _17, T18 _18) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
    public T8 dtor__8 {
      get {
        return this.__8;
      }
    }
    public T9 dtor__9 {
      get {
        return this.__9;
      }
    }
    public T10 dtor__10 {
      get {
        return this.__10;
      }
    }
    public T11 dtor__11 {
      get {
        return this.__11;
      }
    }
    public T12 dtor__12 {
      get {
        return this.__12;
      }
    }
    public T13 dtor__13 {
      get {
        return this.__13;
      }
    }
    public T14 dtor__14 {
      get {
        return this.__14;
      }
    }
    public T15 dtor__15 {
      get {
        return this.__15;
      }
    }
    public T16 dtor__16 {
      get {
        return this.__16;
      }
    }
    public T17 dtor__17 {
      get {
        return this.__17;
      }
    }
    public T18 dtor__18 {
      get {
        return this.__18;
      }
    }
  }

  public interface _ITuple20<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11, out T12, out T13, out T14, out T15, out T16, out T17, out T18, out T19> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    T12 dtor__12 { get; }
    T13 dtor__13 { get; }
    T14 dtor__14 { get; }
    T15 dtor__15 { get; }
    T16 dtor__16 { get; }
    T17 dtor__17 { get; }
    T18 dtor__18 { get; }
    T19 dtor__19 { get; }
    _ITuple20<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18, __T19> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18, __T19>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15, Func<T16, __T16> converter16, Func<T17, __T17> converter17, Func<T18, __T18> converter18, Func<T19, __T19> converter19);
  }
  public class Tuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19> : _ITuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19> {
    public readonly T0 __0;
    public readonly T1 __1;
    public readonly T2 __2;
    public readonly T3 __3;
    public readonly T4 __4;
    public readonly T5 __5;
    public readonly T6 __6;
    public readonly T7 __7;
    public readonly T8 __8;
    public readonly T9 __9;
    public readonly T10 __10;
    public readonly T11 __11;
    public readonly T12 __12;
    public readonly T13 __13;
    public readonly T14 __14;
    public readonly T15 __15;
    public readonly T16 __16;
    public readonly T17 __17;
    public readonly T18 __18;
    public readonly T19 __19;
    public Tuple20(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16, T17 _17, T18 _18, T19 _19) {
      this.__0 = _0;
      this.__1 = _1;
      this.__2 = _2;
      this.__3 = _3;
      this.__4 = _4;
      this.__5 = _5;
      this.__6 = _6;
      this.__7 = _7;
      this.__8 = _8;
      this.__9 = _9;
      this.__10 = _10;
      this.__11 = _11;
      this.__12 = _12;
      this.__13 = _13;
      this.__14 = _14;
      this.__15 = _15;
      this.__16 = _16;
      this.__17 = _17;
      this.__18 = _18;
      this.__19 = _19;
    }
    public _ITuple20<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18, __T19> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18, __T19>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15, Func<T16, __T16> converter16, Func<T17, __T17> converter17, Func<T18, __T18> converter18, Func<T19, __T19> converter19) {
      if (this is _ITuple20<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18, __T19> dt) { return dt; }
      return new Tuple20<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18, __T19>(converter0(__0), converter1(__1), converter2(__2), converter3(__3), converter4(__4), converter5(__5), converter6(__6), converter7(__7), converter8(__8), converter9(__9), converter10(__10), converter11(__11), converter12(__12), converter13(__13), converter14(__14), converter15(__15), converter16(__16), converter17(__17), converter18(__18), converter19(__19));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19>;
      return oth != null && object.Equals(this.__0, oth.__0) && object.Equals(this.__1, oth.__1) && object.Equals(this.__2, oth.__2) && object.Equals(this.__3, oth.__3) && object.Equals(this.__4, oth.__4) && object.Equals(this.__5, oth.__5) && object.Equals(this.__6, oth.__6) && object.Equals(this.__7, oth.__7) && object.Equals(this.__8, oth.__8) && object.Equals(this.__9, oth.__9) && object.Equals(this.__10, oth.__10) && object.Equals(this.__11, oth.__11) && object.Equals(this.__12, oth.__12) && object.Equals(this.__13, oth.__13) && object.Equals(this.__14, oth.__14) && object.Equals(this.__15, oth.__15) && object.Equals(this.__16, oth.__16) && object.Equals(this.__17, oth.__17) && object.Equals(this.__18, oth.__18) && object.Equals(this.__19, oth.__19);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__11));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__12));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__13));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__14));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__15));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__16));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__17));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__18));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.__19));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.__0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__2);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__3);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__4);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__5);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__6);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__7);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__8);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__9);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__10);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__11);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__12);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__13);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__14);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__15);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__16);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__17);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__18);
      s += ", ";
      s += Dafny.Helpers.ToString(this.__19);
      s += ")";
      return s;
    }
    public static _System._ITuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11, T12 _default_T12, T13 _default_T13, T14 _default_T14, T15 _default_T15, T16 _default_T16, T17 _default_T17, T18 _default_T18, T19 _default_T19) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11, _default_T12, _default_T13, _default_T14, _default_T15, _default_T16, _default_T17, _default_T18, _default_T19);
    }
    public static Dafny.TypeDescriptor<_System._ITuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11, Dafny.TypeDescriptor<T12> _td_T12, Dafny.TypeDescriptor<T13> _td_T13, Dafny.TypeDescriptor<T14> _td_T14, Dafny.TypeDescriptor<T15> _td_T15, Dafny.TypeDescriptor<T16> _td_T16, Dafny.TypeDescriptor<T17> _td_T17, Dafny.TypeDescriptor<T18> _td_T18, Dafny.TypeDescriptor<T19> _td_T19) {
      return new Dafny.TypeDescriptor<_System._ITuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19>>(_System.Tuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default(), _td_T12.Default(), _td_T13.Default(), _td_T14.Default(), _td_T15.Default(), _td_T16.Default(), _td_T17.Default(), _td_T18.Default(), _td_T19.Default()));
    }
    public static _ITuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16, T17 _17, T18 _18, T19 _19) {
      return new Tuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, _19);
    }
    public static _ITuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19> create____hMake20(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16, T17 _17, T18 _18, T19 _19) {
      return create(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, _19);
    }
    public T0 dtor__0 {
      get {
        return this.__0;
      }
    }
    public T1 dtor__1 {
      get {
        return this.__1;
      }
    }
    public T2 dtor__2 {
      get {
        return this.__2;
      }
    }
    public T3 dtor__3 {
      get {
        return this.__3;
      }
    }
    public T4 dtor__4 {
      get {
        return this.__4;
      }
    }
    public T5 dtor__5 {
      get {
        return this.__5;
      }
    }
    public T6 dtor__6 {
      get {
        return this.__6;
      }
    }
    public T7 dtor__7 {
      get {
        return this.__7;
      }
    }
    public T8 dtor__8 {
      get {
        return this.__8;
      }
    }
    public T9 dtor__9 {
      get {
        return this.__9;
      }
    }
    public T10 dtor__10 {
      get {
        return this.__10;
      }
    }
    public T11 dtor__11 {
      get {
        return this.__11;
      }
    }
    public T12 dtor__12 {
      get {
        return this.__12;
      }
    }
    public T13 dtor__13 {
      get {
        return this.__13;
      }
    }
    public T14 dtor__14 {
      get {
        return this.__14;
      }
    }
    public T15 dtor__15 {
      get {
        return this.__15;
      }
    }
    public T16 dtor__16 {
      get {
        return this.__16;
      }
    }
    public T17 dtor__17 {
      get {
        return this.__17;
      }
    }
    public T18 dtor__18 {
      get {
        return this.__18;
      }
    }
    public T19 dtor__19 {
      get {
        return this.__19;
      }
    }
  }
} // end of namespace _System
namespace Dafny {
  internal class ArrayHelpers {
    public static T[] InitNewArray1<T>(T z, BigInteger size0) {
      int s0 = (int)size0;
      T[] a = new T[s0];
      for (int i0 = 0; i0 < s0; i0++) {
        a[i0] = z;
      }
      return a;
    }
  }
} // end of namespace Dafny
internal static class FuncExtensions {
  public static Func<U, UResult> DowncastClone<T, TResult, U, UResult>(this Func<T, TResult> F, Func<U, T> ArgConv, Func<TResult, UResult> ResConv) {
    return arg => ResConv(F(ArgConv(arg)));
  }
  public static Func<UResult> DowncastClone<TResult, UResult>(this Func<TResult> F, Func<TResult, UResult> ResConv) {
    return () => ResConv(F());
  }
  public static Func<U1, U2, UResult> DowncastClone<T1, T2, TResult, U1, U2, UResult>(this Func<T1, T2, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<TResult, UResult> ResConv) {
    return (arg1, arg2) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2)));
  }
  public static Func<U1, U2, U3, U4, UResult> DowncastClone<T1, T2, T3, T4, TResult, U1, U2, U3, U4, UResult>(this Func<T1, T2, T3, T4, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4)));
  }
  public static Func<U1, U2, U3, UResult> DowncastClone<T1, T2, T3, TResult, U1, U2, U3, UResult>(this Func<T1, T2, T3, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3)));
  }
}
// end of class FuncExtensions
namespace Wrappers {

  public partial class __default {
    public static Wrappers._IOutcome<__E> Need<__E>(bool condition, __E error)
    {
      if (condition) {
        return Wrappers.Outcome<__E>.create_Pass();
      } else {
        return Wrappers.Outcome<__E>.create_Fail(error);
      }
    }
  }

  public interface _IOption<out T> {
    bool is_None { get; }
    bool is_Some { get; }
    T dtor_value { get; }
    _IOption<__T> DowncastClone<__T>(Func<T, __T> converter0);
    Wrappers._IResult<T, Dafny.ISequence<char>> ToResult();
    Wrappers._IResult<T, __R> ToResult_k<__R>(__R error);
    bool IsFailure();
    Wrappers._IOption<__U> PropagateFailure<__U>();
    T Extract();
  }
  public abstract class Option<T> : _IOption<T> {
    public Option() {
    }
    public static Wrappers._IOption<T> Default() {
      return create_None();
    }
    public static Dafny.TypeDescriptor<Wrappers._IOption<T>> _TypeDescriptor() {
      return new Dafny.TypeDescriptor<Wrappers._IOption<T>>(Wrappers.Option<T>.Default());
    }
    public static _IOption<T> create_None() {
      return new Option_None<T>();
    }
    public static _IOption<T> create_Some(T @value) {
      return new Option_Some<T>(@value);
    }
    public bool is_None { get { return this is Option_None<T>; } }
    public bool is_Some { get { return this is Option_Some<T>; } }
    public T dtor_value {
      get {
        var d = this;
        return ((Option_Some<T>)d)._value;
      }
    }
    public abstract _IOption<__T> DowncastClone<__T>(Func<T, __T> converter0);
    public Wrappers._IResult<T, Dafny.ISequence<char>> ToResult() {
      Wrappers._IOption<T> _source0 = this;
      {
        if (_source0.is_Some) {
          T _0_v = _source0.dtor_value;
          return Wrappers.Result<T, Dafny.ISequence<char>>.create_Success(_0_v);
        }
      }
      {
        return Wrappers.Result<T, Dafny.ISequence<char>>.create_Failure(Dafny.Sequence<char>.FromString("Option is None"));
      }
    }
    public Wrappers._IResult<T, __R> ToResult_k<__R>(__R error) {
      Wrappers._IOption<T> _source0 = this;
      {
        if (_source0.is_Some) {
          T _0_v = _source0.dtor_value;
          return Wrappers.Result<T, __R>.create_Success(_0_v);
        }
      }
      {
        return Wrappers.Result<T, __R>.create_Failure(error);
      }
    }
    public static T UnwrapOr(Wrappers._IOption<T> _this, T @default) {
      Wrappers._IOption<T> _source0 = _this;
      {
        if (_source0.is_Some) {
          T _0_v = _source0.dtor_value;
          return _0_v;
        }
      }
      {
        return @default;
      }
    }
    public bool IsFailure() {
      return (this).is_None;
    }
    public Wrappers._IOption<__U> PropagateFailure<__U>() {
      return Wrappers.Option<__U>.create_None();
    }
    public T Extract() {
      return (this).dtor_value;
    }
  }
  public class Option_None<T> : Option<T> {
    public Option_None() : base() {
    }
    public override _IOption<__T> DowncastClone<__T>(Func<T, __T> converter0) {
      if (this is _IOption<__T> dt) { return dt; }
      return new Option_None<__T>();
    }
    public override bool Equals(object other) {
      var oth = other as Wrappers.Option_None<T>;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Wrappers.Option.None";
      return s;
    }
  }
  public class Option_Some<T> : Option<T> {
    public readonly T _value;
    public Option_Some(T @value) : base() {
      this._value = @value;
    }
    public override _IOption<__T> DowncastClone<__T>(Func<T, __T> converter0) {
      if (this is _IOption<__T> dt) { return dt; }
      return new Option_Some<__T>(converter0(_value));
    }
    public override bool Equals(object other) {
      var oth = other as Wrappers.Option_Some<T>;
      return oth != null && object.Equals(this._value, oth._value);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._value));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Wrappers.Option.Some";
      s += "(";
      s += Dafny.Helpers.ToString(this._value);
      s += ")";
      return s;
    }
  }

  public interface _IResult<out T, out R> {
    bool is_Success { get; }
    bool is_Failure { get; }
    T dtor_value { get; }
    R dtor_error { get; }
    _IResult<__T, __R> DowncastClone<__T, __R>(Func<T, __T> converter0, Func<R, __R> converter1);
    Wrappers._IOption<T> ToOption();
    bool IsFailure();
    Wrappers._IResult<__U, R> PropagateFailure<__U>();
    T Extract();
  }
  public abstract class Result<T, R> : _IResult<T, R> {
    public Result() {
    }
    public static Wrappers._IResult<T, R> Default(T _default_T) {
      return create_Success(_default_T);
    }
    public static Dafny.TypeDescriptor<Wrappers._IResult<T, R>> _TypeDescriptor(Dafny.TypeDescriptor<T> _td_T) {
      return new Dafny.TypeDescriptor<Wrappers._IResult<T, R>>(Wrappers.Result<T, R>.Default(_td_T.Default()));
    }
    public static _IResult<T, R> create_Success(T @value) {
      return new Result_Success<T, R>(@value);
    }
    public static _IResult<T, R> create_Failure(R error) {
      return new Result_Failure<T, R>(error);
    }
    public bool is_Success { get { return this is Result_Success<T, R>; } }
    public bool is_Failure { get { return this is Result_Failure<T, R>; } }
    public T dtor_value {
      get {
        var d = this;
        return ((Result_Success<T, R>)d)._value;
      }
    }
    public R dtor_error {
      get {
        var d = this;
        return ((Result_Failure<T, R>)d)._error;
      }
    }
    public abstract _IResult<__T, __R> DowncastClone<__T, __R>(Func<T, __T> converter0, Func<R, __R> converter1);
    public Wrappers._IOption<T> ToOption() {
      Wrappers._IResult<T, R> _source0 = this;
      {
        if (_source0.is_Success) {
          T _0_s = _source0.dtor_value;
          return Wrappers.Option<T>.create_Some(_0_s);
        }
      }
      {
        R _1_e = _source0.dtor_error;
        return Wrappers.Option<T>.create_None();
      }
    }
    public static T UnwrapOr(Wrappers._IResult<T, R> _this, T @default) {
      Wrappers._IResult<T, R> _source0 = _this;
      {
        if (_source0.is_Success) {
          T _0_s = _source0.dtor_value;
          return _0_s;
        }
      }
      {
        R _1_e = _source0.dtor_error;
        return @default;
      }
    }
    public bool IsFailure() {
      return (this).is_Failure;
    }
    public Wrappers._IResult<__U, R> PropagateFailure<__U>() {
      return Wrappers.Result<__U, R>.create_Failure((this).dtor_error);
    }
    public static Wrappers._IResult<T, __NewR> MapFailure<__NewR>(Wrappers._IResult<T, R> _this, Func<R, __NewR> reWrap) {
      Wrappers._IResult<T, R> _source0 = _this;
      {
        if (_source0.is_Success) {
          T _0_s = _source0.dtor_value;
          return Wrappers.Result<T, __NewR>.create_Success(_0_s);
        }
      }
      {
        R _1_e = _source0.dtor_error;
        return Wrappers.Result<T, __NewR>.create_Failure(Dafny.Helpers.Id<Func<R, __NewR>>(reWrap)(_1_e));
      }
    }
    public T Extract() {
      return (this).dtor_value;
    }
  }
  public class Result_Success<T, R> : Result<T, R> {
    public readonly T _value;
    public Result_Success(T @value) : base() {
      this._value = @value;
    }
    public override _IResult<__T, __R> DowncastClone<__T, __R>(Func<T, __T> converter0, Func<R, __R> converter1) {
      if (this is _IResult<__T, __R> dt) { return dt; }
      return new Result_Success<__T, __R>(converter0(_value));
    }
    public override bool Equals(object other) {
      var oth = other as Wrappers.Result_Success<T, R>;
      return oth != null && object.Equals(this._value, oth._value);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._value));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Wrappers.Result.Success";
      s += "(";
      s += Dafny.Helpers.ToString(this._value);
      s += ")";
      return s;
    }
  }
  public class Result_Failure<T, R> : Result<T, R> {
    public readonly R _error;
    public Result_Failure(R error) : base() {
      this._error = error;
    }
    public override _IResult<__T, __R> DowncastClone<__T, __R>(Func<T, __T> converter0, Func<R, __R> converter1) {
      if (this is _IResult<__T, __R> dt) { return dt; }
      return new Result_Failure<__T, __R>(converter1(_error));
    }
    public override bool Equals(object other) {
      var oth = other as Wrappers.Result_Failure<T, R>;
      return oth != null && object.Equals(this._error, oth._error);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._error));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Wrappers.Result.Failure";
      s += "(";
      s += Dafny.Helpers.ToString(this._error);
      s += ")";
      return s;
    }
  }

  public interface _IOutcome<E> {
    bool is_Pass { get; }
    bool is_Fail { get; }
    E dtor_error { get; }
    _IOutcome<__E> DowncastClone<__E>(Func<E, __E> converter0);
    bool IsFailure();
    Wrappers._IResult<__U, E> PropagateFailure<__U>();
  }
  public abstract class Outcome<E> : _IOutcome<E> {
    public Outcome() {
    }
    public static Wrappers._IOutcome<E> Default() {
      return create_Pass();
    }
    public static Dafny.TypeDescriptor<Wrappers._IOutcome<E>> _TypeDescriptor() {
      return new Dafny.TypeDescriptor<Wrappers._IOutcome<E>>(Wrappers.Outcome<E>.Default());
    }
    public static _IOutcome<E> create_Pass() {
      return new Outcome_Pass<E>();
    }
    public static _IOutcome<E> create_Fail(E error) {
      return new Outcome_Fail<E>(error);
    }
    public bool is_Pass { get { return this is Outcome_Pass<E>; } }
    public bool is_Fail { get { return this is Outcome_Fail<E>; } }
    public E dtor_error {
      get {
        var d = this;
        return ((Outcome_Fail<E>)d)._error;
      }
    }
    public abstract _IOutcome<__E> DowncastClone<__E>(Func<E, __E> converter0);
    public bool IsFailure() {
      return (this).is_Fail;
    }
    public Wrappers._IResult<__U, E> PropagateFailure<__U>() {
      return Wrappers.Result<__U, E>.create_Failure((this).dtor_error);
    }
  }
  public class Outcome_Pass<E> : Outcome<E> {
    public Outcome_Pass() : base() {
    }
    public override _IOutcome<__E> DowncastClone<__E>(Func<E, __E> converter0) {
      if (this is _IOutcome<__E> dt) { return dt; }
      return new Outcome_Pass<__E>();
    }
    public override bool Equals(object other) {
      var oth = other as Wrappers.Outcome_Pass<E>;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Wrappers.Outcome.Pass";
      return s;
    }
  }
  public class Outcome_Fail<E> : Outcome<E> {
    public readonly E _error;
    public Outcome_Fail(E error) : base() {
      this._error = error;
    }
    public override _IOutcome<__E> DowncastClone<__E>(Func<E, __E> converter0) {
      if (this is _IOutcome<__E> dt) { return dt; }
      return new Outcome_Fail<__E>(converter0(_error));
    }
    public override bool Equals(object other) {
      var oth = other as Wrappers.Outcome_Fail<E>;
      return oth != null && object.Equals(this._error, oth._error);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._error));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Wrappers.Outcome.Fail";
      s += "(";
      s += Dafny.Helpers.ToString(this._error);
      s += ")";
      return s;
    }
  }
} // end of namespace Wrappers
namespace FileIO {

  public partial class __default {
    public static Wrappers._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>> ReadBytesFromFile(Dafny.ISequence<char> path)
    {
      Wrappers._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>> res = Wrappers.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(Dafny.Sequence<byte>.Empty);
      bool _0_isError;
      Dafny.ISequence<byte> _1_bytesRead;
      Dafny.ISequence<char> _2_errorMsg;
      bool _out0;
      Dafny.ISequence<byte> _out1;
      Dafny.ISequence<char> _out2;
      DafnyLibraries.FileIO.INTERNAL_ReadBytesFromFile(path, out _out0, out _out1, out _out2);
      _0_isError = _out0;
      _1_bytesRead = _out1;
      _2_errorMsg = _out2;
      if (_0_isError) {
        res = Wrappers.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.create_Failure(_2_errorMsg);
      } else {
        res = Wrappers.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.create_Success(_1_bytesRead);
      }
      return res;
      return res;
    }
    public static Wrappers._IResult<_System._ITuple0, Dafny.ISequence<char>> WriteBytesToFile(Dafny.ISequence<char> path, Dafny.ISequence<byte> bytes)
    {
      Wrappers._IResult<_System._ITuple0, Dafny.ISequence<char>> res = Wrappers.Result<_System._ITuple0, Dafny.ISequence<char>>.Default(_System.Tuple0.Default());
      bool _0_isError;
      Dafny.ISequence<char> _1_errorMsg;
      bool _out0;
      Dafny.ISequence<char> _out1;
      DafnyLibraries.FileIO.INTERNAL_WriteBytesToFile(path, bytes, out _out0, out _out1);
      _0_isError = _out0;
      _1_errorMsg = _out1;
      if (_0_isError) {
        res = Wrappers.Result<_System._ITuple0, Dafny.ISequence<char>>.create_Failure(_1_errorMsg);
      } else {
        res = Wrappers.Result<_System._ITuple0, Dafny.ISequence<char>>.create_Success(_System.Tuple0.create());
      }
      return res;
      return res;
    }
  }
} // end of namespace FileIO
namespace StringUtils {

  public partial class __default {
    public static Dafny.BigRational ParseReal(Dafny.ISequence<char> s)
    {
      Dafny.BigRational r = Dafny.BigRational.ZERO;
      bool _0_neg;
      _0_neg = false;
      BigInteger _1_i;
      _1_i = BigInteger.Zero;
      if (((s).Select(_1_i)) == ('-')) {
        _0_neg = true;
        _1_i = (_1_i) + (BigInteger.One);
      }
      r = new Dafny.BigRational((StringUtils.__default.ParseDigit((s).Select(_1_i))), BigInteger.One);
      _1_i = (_1_i) + (BigInteger.One);
      BigInteger _2_periodIndex;
      _2_periodIndex = BigInteger.One;
      while ((_1_i) < (new BigInteger((s).Count))) {
        if (StringUtils.__default.IsDigit((s).Select(_1_i))) {
          r = ((r) * (new Dafny.BigRational(BigInteger.Parse("10"), BigInteger.One))) + (new Dafny.BigRational((StringUtils.__default.ParseDigit((s).Select(_1_i))), BigInteger.One));
        } else {
          _2_periodIndex = _1_i;
        }
        _1_i = (_1_i) + (BigInteger.One);
      }
      _1_i = BigInteger.Zero;
      while ((_1_i) < (((new BigInteger((s).Count)) - (_2_periodIndex)) - (BigInteger.One))) {
        r = (r) / (new Dafny.BigRational(BigInteger.Parse("10"), BigInteger.One));
        _1_i = (_1_i) + (BigInteger.One);
      }
      if (_0_neg) {
        r = (r) * (new Dafny.BigRational(BigInteger.Parse("-1"), BigInteger.One));
      }
      return r;
    }
    public static BigInteger ParseInt(Dafny.ISequence<char> s)
    {
      BigInteger r = BigInteger.Zero;
      bool _0_neg;
      _0_neg = false;
      BigInteger _1_i;
      _1_i = BigInteger.Zero;
      if (((s).Select(_1_i)) == ('-')) {
        _0_neg = true;
        _1_i = (_1_i) + (BigInteger.One);
      }
      r = StringUtils.__default.ParseDigit((s).Select(_1_i));
      _1_i = (_1_i) + (BigInteger.One);
      BigInteger _2_periodIndex;
      _2_periodIndex = BigInteger.One;
      while ((_1_i) < (new BigInteger((s).Count))) {
        if (StringUtils.__default.IsDigit((s).Select(_1_i))) {
          r = ((r) * (new BigInteger(10))) + (StringUtils.__default.ParseDigit((s).Select(_1_i)));
        }
        _1_i = (_1_i) + (BigInteger.One);
      }
      if (_0_neg) {
        r = (r) * (new BigInteger(-1));
      }
      return r;
    }
    public static BigInteger ParseDigit(char x) {
      if ((x) == ('0')) {
        return BigInteger.Zero;
      } else if ((x) == ('1')) {
        return BigInteger.One;
      } else if ((x) == ('2')) {
        return new BigInteger(2);
      } else if ((x) == ('3')) {
        return new BigInteger(3);
      } else if ((x) == ('4')) {
        return new BigInteger(4);
      } else if ((x) == ('5')) {
        return new BigInteger(5);
      } else if ((x) == ('6')) {
        return new BigInteger(6);
      } else if ((x) == ('7')) {
        return new BigInteger(7);
      } else if ((x) == ('8')) {
        return new BigInteger(8);
      } else {
        return new BigInteger(9);
      }
    }
    public static bool IsReal(Dafny.ISequence<char> s) {
      return ((((new BigInteger((s).Count)) >= (new BigInteger(3))) && ((StringUtils.__default.IsDigit((s).Select(BigInteger.Zero))) || ((((s).Select(BigInteger.Zero)) == ('-')) && (StringUtils.__default.IsDigit((s).Select(BigInteger.One)))))) && (StringUtils.__default.IsDigit((s).Select((new BigInteger((s).Count)) - (BigInteger.One))))) && (Dafny.Helpers.Id<Func<Dafny.ISequence<char>, bool>>((_0_s) => Dafny.Helpers.Quantifier<BigInteger>(Dafny.Helpers.IntegerRange(BigInteger.Zero, new BigInteger((_0_s).Count)), false, (((_exists_var_0) => {
        BigInteger _1_i = (BigInteger)_exists_var_0;
        return ((((_1_i).Sign != -1) && ((_1_i) < (new BigInteger((_0_s).Count)))) && (((_0_s).Select(_1_i)) == ('.'))) && (Dafny.Helpers.Id<Func<Dafny.ISequence<char>, BigInteger, bool>>((_2_s, _3_i) => Dafny.Helpers.Quantifier<BigInteger>(Dafny.Helpers.IntegerRange(BigInteger.One, new BigInteger((_2_s).Count)), true, (((_forall_var_0) => {
          BigInteger _4_j = (BigInteger)_forall_var_0;
          return !((((BigInteger.One) <= (_4_j)) && ((_4_j) < (new BigInteger((_2_s).Count)))) && ((_4_j) != (_3_i))) || (StringUtils.__default.IsDigit((_2_s).Select(_4_j)));
        }))))(_0_s, _1_i));
      }))))(s));
    }
    public static bool IsInt(Dafny.ISequence<char> s) {
      return ((((new BigInteger((s).Count)) >= (BigInteger.One)) && ((StringUtils.__default.IsDigit((s).Select(BigInteger.Zero))) || (((new BigInteger((s).Count)) >= (new BigInteger(2))) && ((((s).Select(BigInteger.Zero)) == ('-')) && (StringUtils.__default.IsDigit((s).Select(BigInteger.One))))))) && (StringUtils.__default.IsDigit((s).Select((new BigInteger((s).Count)) - (BigInteger.One))))) && (Dafny.Helpers.Id<Func<Dafny.ISequence<char>, bool>>((_0_s) => Dafny.Helpers.Quantifier<BigInteger>(Dafny.Helpers.IntegerRange(BigInteger.One, new BigInteger((_0_s).Count)), true, (((_forall_var_0) => {
        BigInteger _1_j = (BigInteger)_forall_var_0;
        return !(((BigInteger.One) <= (_1_j)) && ((_1_j) < (new BigInteger((_0_s).Count)))) || (StringUtils.__default.IsDigit((_0_s).Select(_1_j)));
      }))))(s));
    }
    public static bool IsDigit(char x) {
      return ((((((((((x) == ('0')) || ((x) == ('1'))) || ((x) == ('2'))) || ((x) == ('3'))) || ((x) == ('4'))) || ((x) == ('5'))) || ((x) == ('6'))) || ((x) == ('7'))) || ((x) == ('8'))) || ((x) == ('9'));
    }
    public static Dafny.ISequence<Dafny.ISequence<char>> Split(Dafny.ISequence<char> xs, char x)
    {
      Dafny.ISequence<Dafny.ISequence<char>> r = Dafny.Sequence<Dafny.ISequence<char>>.Empty;
      Dafny.ISequence<BigInteger> _0_splits;
      _0_splits = StringUtils.__default.Indices(xs, x);
      if ((_0_splits).Equals(Dafny.Sequence<BigInteger>.FromElements())) {
        r = Dafny.Sequence<Dafny.ISequence<char>>.FromElements(xs);
        return r;
      }
      r = Dafny.Sequence<Dafny.ISequence<char>>.FromElements((xs).Take((_0_splits).Select(BigInteger.Zero)));
      BigInteger _1_i;
      _1_i = BigInteger.One;
      while ((_1_i) < (new BigInteger((_0_splits).Count))) {
        r = Dafny.Sequence<Dafny.ISequence<char>>.Concat(r, Dafny.Sequence<Dafny.ISequence<char>>.FromElements((xs).Subsequence(((_0_splits).Select((_1_i) - (BigInteger.One))) + (BigInteger.One), (_0_splits).Select(_1_i))));
        _1_i = (_1_i) + (BigInteger.One);
      }
      r = Dafny.Sequence<Dafny.ISequence<char>>.Concat(r, Dafny.Sequence<Dafny.ISequence<char>>.FromElements(((xs).Drop((_0_splits).Select((new BigInteger((_0_splits).Count)) - (BigInteger.One)))).Drop(BigInteger.One)));
      return r;
    }
    public static Dafny.ISequence<BigInteger> Indices(Dafny.ISequence<char> xs, char x)
    {
      Dafny.ISequence<BigInteger> _0___accumulator = Dafny.Sequence<BigInteger>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return Dafny.Sequence<BigInteger>.Concat(Dafny.Sequence<BigInteger>.FromElements(), _0___accumulator);
      } else if (((xs).Select((new BigInteger((xs).Count)) - (BigInteger.One))) == (x)) {
        _0___accumulator = Dafny.Sequence<BigInteger>.Concat(Dafny.Sequence<BigInteger>.FromElements((new BigInteger((xs).Count)) - (BigInteger.One)), _0___accumulator);
        Dafny.ISequence<char> _in0 = (xs).Take((new BigInteger((xs).Count)) - (BigInteger.One));
        char _in1 = x;
        xs = _in0;
        x = _in1;
        goto TAIL_CALL_START;
      } else {
        Dafny.ISequence<char> _in2 = (xs).Take((new BigInteger((xs).Count)) - (BigInteger.One));
        char _in3 = x;
        xs = _in2;
        x = _in3;
        goto TAIL_CALL_START;
      }
    }
  }
} // end of namespace StringUtils
namespace BasicArithmetic {

  public partial class __default {
    public static Dafny.BigRational Abs(Dafny.BigRational x) {
      if ((x) >= (new Dafny.BigRational(BigInteger.Parse("0"), BigInteger.One))) {
        return x;
      } else {
        return (new Dafny.BigRational(BigInteger.Parse("0"), BigInteger.One)) - (x);
      }
    }
    public static Dafny.BigRational Square(Dafny.BigRational x) {
      return (x) * (x);
    }
    public static Dafny.BigRational Power2RootUpperBound(Dafny.BigRational x, BigInteger i)
    {
      Dafny.BigRational r = Dafny.BigRational.ZERO;
      BigInteger _0_j;
      _0_j = i;
      r = x;
      while ((_0_j).Sign == 1) {
        Dafny.BigRational _out0;
        _out0 = BasicArithmetic.__default.SqrtUpperBound(r);
        r = _out0;
        _0_j = (_0_j) - (BigInteger.One);
      }
      return r;
    }
    public static Dafny.BigRational SqrtUpperBound(Dafny.BigRational x)
    {
      Dafny.BigRational r = Dafny.BigRational.ZERO;
      if ((x) == (new Dafny.BigRational(BigInteger.Parse("0"), BigInteger.One))) {
        r = new Dafny.BigRational(BigInteger.Parse("0"), BigInteger.One);
        return r;
      }
      if ((x) < (new Dafny.BigRational(BigInteger.Parse("1"), BigInteger.One))) {
        r = new Dafny.BigRational(BigInteger.Parse("1"), BigInteger.One);
      } else {
        r = x;
      }
      BigInteger _0_i;
      _0_i = BigInteger.Zero;
      while ((_0_i) < (BasicArithmetic.__default.SQRT__ITERATIONS)) {
        Dafny.BigRational _1_old__r;
        _1_old__r = r;
        Dafny.BigRational _out0;
        _out0 = BasicArithmetic.__default.RoundUp(((r) + ((x) / (r))) / (new Dafny.BigRational(BigInteger.Parse("2"), BigInteger.One)));
        r = _out0;
        _0_i = (_0_i) + (BigInteger.One);
        if (((_1_old__r) - (r)) < (BasicArithmetic.__default.SQRT__ERR__MARGIN)) {
          return r;
        }
      }
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("WARNING: Sqrt algorithm terminated early after reaching ")));
      Dafny.Helpers.Print((BasicArithmetic.__default.SQRT__ITERATIONS));
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(" iterations.\n")));
      return r;
    }
    public static Dafny.BigRational RoundUp(Dafny.BigRational x)
    {
      Dafny.BigRational r = Dafny.BigRational.ZERO;
      BigInteger _0_i;
      _0_i = BigInteger.Zero;
      r = x;
      while (((r) != (new Dafny.BigRational(((r).ToBigInteger()), BigInteger.One))) && ((_0_i) < (BasicArithmetic.__default.ROUNDING__PRECISION))) {
        r = (r) * (new Dafny.BigRational(BigInteger.Parse("10"), BigInteger.One));
        _0_i = (_0_i) + (BigInteger.One);
      }
      if ((r) != (new Dafny.BigRational(((r).ToBigInteger()), BigInteger.One))) {
        r = (r) + (new Dafny.BigRational(BigInteger.Parse("1"), BigInteger.One));
      }
      r = new Dafny.BigRational(((r).ToBigInteger()), BigInteger.One);
      while ((_0_i).Sign == 1) {
        r = (r) / (new Dafny.BigRational(BigInteger.Parse("10"), BigInteger.One));
        _0_i = (_0_i) - (BigInteger.One);
      }
      return r;
    }
    public static void PrintReal(Dafny.BigRational x, BigInteger n)
    {
      BigInteger _0_z;
      _0_z = (x).ToBigInteger();
      Dafny.Helpers.Print((_0_z));
      Dafny.Helpers.Print(('.'));
      Dafny.BigRational _1_y;
      _1_y = x;
      BigInteger _2_i;
      _2_i = BigInteger.Zero;
      while ((_2_i) < (n)) {
        _1_y = (_1_y) * (new Dafny.BigRational(BigInteger.Parse("10"), BigInteger.One));
        _0_z = (_0_z) * (new BigInteger(10));
        _2_i = (_2_i) + (BigInteger.One);
      }
      Dafny.Helpers.Print((((_1_y).ToBigInteger()) - (_0_z)));
    }
    public static BigInteger SQRT__ITERATIONS { get {
      return new BigInteger(5000);
    } }
    public static BigInteger ROUNDING__PRECISION { get {
      return new BigInteger(16);
    } }
    public static Dafny.BigRational SQRT__ERR__MARGIN { get {
      return new Dafny.BigRational(BigInteger.One, BigInteger.Parse("10000000"));
    } }
    public static bool DEBUG { get {
      return true;
    } }
  }
} // end of namespace BasicArithmetic
namespace Lipschitz {

  public partial class __default {
    public static Dafny.ISequence<Dafny.BigRational> NonEmptyVector() {
      return Dafny.Sequence<Dafny.BigRational>.FromElements(new Dafny.BigRational(BigInteger.Parse("0"), BigInteger.One));
    }
    public static Dafny.ISequence<Dafny.ISequence<Dafny.BigRational>> NonEmptyMatrix() {
      return Dafny.Sequence<Dafny.ISequence<Dafny.BigRational>>.FromElements(Dafny.Sequence<Dafny.BigRational>.FromElements(new Dafny.BigRational(BigInteger.Parse("0"), BigInteger.One)));
    }
    public static Dafny.BigRational Product(Dafny.ISequence<Dafny.BigRational> s) {
      Dafny.BigRational _0___accumulator = new Dafny.BigRational(BigInteger.Parse("1"), BigInteger.One);
    TAIL_CALL_START: ;
      if ((new BigInteger((s).Count)).Sign == 0) {
        return (new Dafny.BigRational(BigInteger.Parse("1"), BigInteger.One)) * (_0___accumulator);
      } else {
        _0___accumulator = ((s).Select((new BigInteger((s).Count)) - (BigInteger.One))) * (_0___accumulator);
        Dafny.ISequence<Dafny.BigRational> _in0 = (s).Take((new BigInteger((s).Count)) - (BigInteger.One));
        s = _in0;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.BigRational Sum(Dafny.ISequence<Dafny.BigRational> s) {
      Dafny.BigRational _0___accumulator = new Dafny.BigRational(BigInteger.Parse("0"), BigInteger.One);
    TAIL_CALL_START: ;
      if ((new BigInteger((s).Count)).Sign == 0) {
        return (new Dafny.BigRational(BigInteger.Parse("0"), BigInteger.One)) + (_0___accumulator);
      } else {
        _0___accumulator = ((s).Select((new BigInteger((s).Count)) - (BigInteger.One))) + (_0___accumulator);
        Dafny.ISequence<Dafny.BigRational> _in0 = (s).Take((new BigInteger((s).Count)) - (BigInteger.One));
        s = _in0;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<Dafny.BigRational> Minus(Dafny.ISequence<Dafny.BigRational> v, Dafny.ISequence<Dafny.BigRational> u)
    {
      Dafny.ISequence<Dafny.BigRational> _0___accumulator = Dafny.Sequence<Dafny.BigRational>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((v).Count)) == (BigInteger.One)) {
        return Dafny.Sequence<Dafny.BigRational>.Concat(_0___accumulator, Dafny.Sequence<Dafny.BigRational>.FromElements(((v).Select(BigInteger.Zero)) - ((u).Select(BigInteger.Zero))));
      } else {
        _0___accumulator = Dafny.Sequence<Dafny.BigRational>.Concat(_0___accumulator, Dafny.Sequence<Dafny.BigRational>.FromElements(((v).Select(BigInteger.Zero)) - ((u).Select(BigInteger.Zero))));
        Dafny.ISequence<Dafny.BigRational> _in0 = (v).Drop(BigInteger.One);
        Dafny.ISequence<Dafny.BigRational> _in1 = (u).Drop(BigInteger.One);
        v = _in0;
        u = _in1;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<Dafny.BigRational> Apply(Dafny.ISequence<Dafny.BigRational> v, Func<Dafny.BigRational, Dafny.BigRational> f)
    {
      Dafny.ISequence<Dafny.BigRational> _0___accumulator = Dafny.Sequence<Dafny.BigRational>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((v).Count)) == (BigInteger.One)) {
        return Dafny.Sequence<Dafny.BigRational>.Concat(_0___accumulator, Dafny.Sequence<Dafny.BigRational>.FromElements(Dafny.Helpers.Id<Func<Dafny.BigRational, Dafny.BigRational>>(f)((v).Select(BigInteger.Zero))));
      } else {
        _0___accumulator = Dafny.Sequence<Dafny.BigRational>.Concat(_0___accumulator, Dafny.Sequence<Dafny.BigRational>.FromElements(Dafny.Helpers.Id<Func<Dafny.BigRational, Dafny.BigRational>>(f)((v).Select(BigInteger.Zero))));
        Dafny.ISequence<Dafny.BigRational> _in0 = (v).Drop(BigInteger.One);
        Func<Dafny.BigRational, Dafny.BigRational> _in1 = f;
        v = _in0;
        f = _in1;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.BigRational Dot(Dafny.ISequence<Dafny.BigRational> v, Dafny.ISequence<Dafny.BigRational> u)
    {
      Dafny.BigRational _0___accumulator = new Dafny.BigRational(BigInteger.Parse("0"), BigInteger.One);
    TAIL_CALL_START: ;
      if ((new BigInteger((v).Count)) == (BigInteger.One)) {
        return (((v).Select(BigInteger.Zero)) * ((u).Select(BigInteger.Zero))) + (_0___accumulator);
      } else {
        _0___accumulator = (_0___accumulator) + (((v).Select(BigInteger.Zero)) * ((u).Select(BigInteger.Zero)));
        Dafny.ISequence<Dafny.BigRational> _in0 = (v).Drop(BigInteger.One);
        Dafny.ISequence<Dafny.BigRational> _in1 = (u).Drop(BigInteger.One);
        v = _in0;
        u = _in1;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<Dafny.BigRational> MV(Dafny.ISequence<Dafny.ISequence<Dafny.BigRational>> m, Dafny.ISequence<Dafny.BigRational> v)
    {
      Dafny.ISequence<Dafny.BigRational> _0___accumulator = Dafny.Sequence<Dafny.BigRational>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((m).Count)) == (BigInteger.One)) {
        return Dafny.Sequence<Dafny.BigRational>.Concat(_0___accumulator, Dafny.Sequence<Dafny.BigRational>.FromElements(Lipschitz.__default.Dot((m).Select(BigInteger.Zero), v)));
      } else {
        _0___accumulator = Dafny.Sequence<Dafny.BigRational>.Concat(_0___accumulator, Dafny.Sequence<Dafny.BigRational>.FromElements(Lipschitz.__default.Dot((m).Select(BigInteger.Zero), v)));
        Dafny.ISequence<Dafny.ISequence<Dafny.BigRational>> _in0 = (m).Drop(BigInteger.One);
        Dafny.ISequence<Dafny.BigRational> _in1 = v;
        m = _in0;
        v = _in1;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<Dafny.BigRational> GenerateSpecNorms(Lipschitz.LipschitzBounds L, Dafny.ISequence<Dafny.ISequence<Dafny.ISequence<Dafny.BigRational>>> n)
    {
      Dafny.ISequence<Dafny.BigRational> r = Dafny.Sequence<Dafny.BigRational>.Empty;
      BigInteger _0_i;
      _0_i = BigInteger.Zero;
      r = Dafny.Sequence<Dafny.BigRational>.FromElements();
      while ((_0_i) < (new BigInteger((n).Count))) {
        if (BasicArithmetic.__default.DEBUG) {
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("{ \"debug_msg\": \"Generating spectral norm ")));
          Dafny.Helpers.Print((_0_i));
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(" of ")));
          Dafny.Helpers.Print((new BigInteger((n).Count)));
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("...\" },\n")));
        }
        Dafny.BigRational _1_specNorm;
        Dafny.BigRational _out0;
        _out0 = (L).GramIterationSimple((n).Select(_0_i));
        _1_specNorm = _out0;
        r = Dafny.Sequence<Dafny.BigRational>.Concat(r, Dafny.Sequence<Dafny.BigRational>.FromElements(_1_specNorm));
        _0_i = (_0_i) + (BigInteger.One);
      }
      return r;
    }
    public static Dafny.BigRational SumPositiveMatrix(Dafny.ISequence<Dafny.ISequence<Dafny.BigRational>> m) {
      Dafny.BigRational _0___accumulator = new Dafny.BigRational(BigInteger.Parse("0"), BigInteger.One);
    TAIL_CALL_START: ;
      if ((new BigInteger((m).Count)) == (BigInteger.One)) {
        return (Lipschitz.__default.SumPositive((m).Select(BigInteger.Zero))) + (_0___accumulator);
      } else {
        _0___accumulator = (_0___accumulator) + (Lipschitz.__default.SumPositive((m).Select(BigInteger.Zero)));
        Dafny.ISequence<Dafny.ISequence<Dafny.BigRational>> _in0 = (m).Drop(BigInteger.One);
        m = _in0;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.BigRational SumPositive(Dafny.ISequence<Dafny.BigRational> v) {
      Dafny.BigRational _0___accumulator = new Dafny.BigRational(BigInteger.Parse("0"), BigInteger.One);
    TAIL_CALL_START: ;
      if ((new BigInteger((v).Count)) == (BigInteger.One)) {
        return ((v).Select(BigInteger.Zero)) + (_0___accumulator);
      } else {
        _0___accumulator = (_0___accumulator) + ((v).Select(BigInteger.Zero));
        Dafny.ISequence<Dafny.BigRational> _in0 = (v).Drop(BigInteger.One);
        v = _in0;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<Dafny.ISequence<Dafny.BigRational>> SquareMatrixElements(Dafny.ISequence<Dafny.ISequence<Dafny.BigRational>> m) {
      Dafny.ISequence<Dafny.ISequence<Dafny.BigRational>> _0___accumulator = Dafny.Sequence<Dafny.ISequence<Dafny.BigRational>>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((m).Count)) == (BigInteger.One)) {
        return Dafny.Sequence<Dafny.ISequence<Dafny.BigRational>>.Concat(_0___accumulator, Dafny.Sequence<Dafny.ISequence<Dafny.BigRational>>.FromElements(Lipschitz.__default.Apply((m).Select(BigInteger.Zero), BasicArithmetic.__default.Square)));
      } else {
        _0___accumulator = Dafny.Sequence<Dafny.ISequence<Dafny.BigRational>>.Concat(_0___accumulator, Dafny.Sequence<Dafny.ISequence<Dafny.BigRational>>.FromElements(Lipschitz.__default.Apply((m).Select(BigInteger.Zero), BasicArithmetic.__default.Square)));
        Dafny.ISequence<Dafny.ISequence<Dafny.BigRational>> _in0 = (m).Drop(BigInteger.One);
        m = _in0;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.BigRational FrobeniusNormUpperBound(Dafny.ISequence<Dafny.ISequence<Dafny.BigRational>> m)
    {
      Dafny.BigRational r = Dafny.BigRational.ZERO;
      if (BasicArithmetic.__default.DEBUG) {
        Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("{ \"debug_msg\": \"Computing frobenius norm upper bound for matrix of size ")));
        Dafny.Helpers.Print((new BigInteger((m).Count)));
        Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("x")));
        Dafny.Helpers.Print((new BigInteger(((m).Select(BigInteger.Zero)).Count)));
        Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("\" },\n")));
      }
      Dafny.BigRational _out0;
      _out0 = BasicArithmetic.__default.SqrtUpperBound(Lipschitz.__default.SumPositiveMatrix(Lipschitz.__default.SquareMatrixElements(m)));
      r = _out0;
      return r;
    }
    public static Dafny.BigRational L2UpperBound(Dafny.ISequence<Dafny.BigRational> v)
    {
      Dafny.BigRational r = Dafny.BigRational.ZERO;
      if (BasicArithmetic.__default.DEBUG) {
        Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("{ \"debug_msg\": \"Computing L2 norm for vector of length ")));
        Dafny.Helpers.Print((new BigInteger((v).Count)));
        Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("\" },\n")));
      }
      Dafny.BigRational _out0;
      _out0 = BasicArithmetic.__default.SqrtUpperBound(Lipschitz.__default.Sum(Lipschitz.__default.Apply(v, BasicArithmetic.__default.Square)));
      r = _out0;
      return r;
    }
    public static Dafny.ISequence<Dafny.BigRational> GetFirstColumn(Dafny.ISequence<Dafny.ISequence<Dafny.BigRational>> m) {
      Dafny.ISequence<Dafny.BigRational> _0___accumulator = Dafny.Sequence<Dafny.BigRational>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((m).Count)) == (BigInteger.One)) {
        return Dafny.Sequence<Dafny.BigRational>.Concat(_0___accumulator, Dafny.Sequence<Dafny.BigRational>.FromElements(((m).Select(BigInteger.Zero)).Select(BigInteger.Zero)));
      } else {
        _0___accumulator = Dafny.Sequence<Dafny.BigRational>.Concat(_0___accumulator, Dafny.Sequence<Dafny.BigRational>.FromElements(((m).Select(BigInteger.Zero)).Select(BigInteger.Zero)));
        Dafny.ISequence<Dafny.ISequence<Dafny.BigRational>> _in0 = (m).Drop(BigInteger.One);
        m = _in0;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<Dafny.ISequence<Dafny.BigRational>> RemoveFirstColumn(Dafny.ISequence<Dafny.ISequence<Dafny.BigRational>> m) {
      Dafny.ISequence<Dafny.ISequence<Dafny.BigRational>> _0___accumulator = Dafny.Sequence<Dafny.ISequence<Dafny.BigRational>>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((m).Count)) == (BigInteger.One)) {
        return Dafny.Sequence<Dafny.ISequence<Dafny.BigRational>>.Concat(_0___accumulator, Dafny.Sequence<Dafny.ISequence<Dafny.BigRational>>.FromElements(((m).Select(BigInteger.Zero)).Drop(BigInteger.One)));
      } else {
        _0___accumulator = Dafny.Sequence<Dafny.ISequence<Dafny.BigRational>>.Concat(_0___accumulator, Dafny.Sequence<Dafny.ISequence<Dafny.BigRational>>.FromElements(((m).Select(BigInteger.Zero)).Drop(BigInteger.One)));
        Dafny.ISequence<Dafny.ISequence<Dafny.BigRational>> _in0 = (m).Drop(BigInteger.One);
        m = _in0;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<Dafny.ISequence<Dafny.BigRational>> Transpose(Dafny.ISequence<Dafny.ISequence<Dafny.BigRational>> m) {
      Dafny.ISequence<Dafny.ISequence<Dafny.BigRational>> _0___accumulator = Dafny.Sequence<Dafny.ISequence<Dafny.BigRational>>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger(((m).Select(BigInteger.Zero)).Count)) == (BigInteger.One)) {
        return Dafny.Sequence<Dafny.ISequence<Dafny.BigRational>>.Concat(_0___accumulator, Dafny.Sequence<Dafny.ISequence<Dafny.BigRational>>.FromElements(Lipschitz.__default.GetFirstColumn(m)));
      } else {
        _0___accumulator = Dafny.Sequence<Dafny.ISequence<Dafny.BigRational>>.Concat(_0___accumulator, Dafny.Sequence<Dafny.ISequence<Dafny.BigRational>>.FromElements(Lipschitz.__default.GetFirstColumn(m)));
        Dafny.ISequence<Dafny.ISequence<Dafny.BigRational>> _in0 = Lipschitz.__default.RemoveFirstColumn(m);
        m = _in0;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<Dafny.ISequence<Dafny.BigRational>> MM(Dafny.ISequence<Dafny.ISequence<Dafny.BigRational>> m, Dafny.ISequence<Dafny.ISequence<Dafny.BigRational>> n)
    {
      Dafny.ISequence<Dafny.ISequence<Dafny.BigRational>> _0___accumulator = Dafny.Sequence<Dafny.ISequence<Dafny.BigRational>>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((m).Count)) == (BigInteger.One)) {
        return Dafny.Sequence<Dafny.ISequence<Dafny.BigRational>>.Concat(_0___accumulator, Dafny.Sequence<Dafny.ISequence<Dafny.BigRational>>.FromElements(Lipschitz.__default.MMGetRow((m).Select(BigInteger.Zero), n)));
      } else {
        _0___accumulator = Dafny.Sequence<Dafny.ISequence<Dafny.BigRational>>.Concat(_0___accumulator, Dafny.Sequence<Dafny.ISequence<Dafny.BigRational>>.FromElements(Lipschitz.__default.MMGetRow((m).Select(BigInteger.Zero), n)));
        Dafny.ISequence<Dafny.ISequence<Dafny.BigRational>> _in0 = (m).Drop(BigInteger.One);
        Dafny.ISequence<Dafny.ISequence<Dafny.BigRational>> _in1 = n;
        m = _in0;
        n = _in1;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<Dafny.BigRational> MMGetRow(Dafny.ISequence<Dafny.BigRational> v, Dafny.ISequence<Dafny.ISequence<Dafny.BigRational>> n)
    {
      Dafny.ISequence<Dafny.BigRational> _0___accumulator = Dafny.Sequence<Dafny.BigRational>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger(((n).Select(BigInteger.Zero)).Count)) == (BigInteger.One)) {
        return Dafny.Sequence<Dafny.BigRational>.Concat(_0___accumulator, Dafny.Sequence<Dafny.BigRational>.FromElements(Lipschitz.__default.Dot(v, Lipschitz.__default.GetFirstColumn(n))));
      } else {
        _0___accumulator = Dafny.Sequence<Dafny.BigRational>.Concat(_0___accumulator, Dafny.Sequence<Dafny.BigRational>.FromElements(Lipschitz.__default.Dot(v, Lipschitz.__default.GetFirstColumn(n))));
        Dafny.ISequence<Dafny.BigRational> _in0 = v;
        Dafny.ISequence<Dafny.ISequence<Dafny.BigRational>> _in1 = Lipschitz.__default.RemoveFirstColumn(n);
        v = _in0;
        n = _in1;
        goto TAIL_CALL_START;
      }
    }
    public static bool Certify(Dafny.ISequence<Dafny.BigRational> v_k, Dafny.BigRational e, Dafny.ISequence<Dafny.ISequence<Dafny.BigRational>> L)
    {
      bool b = false;
      BigInteger _0_x;
      _0_x = Lipschitz.__default.ArgMax(v_k);
      BigInteger _1_i;
      _1_i = BigInteger.Zero;
      b = true;
      while ((_1_i) < (new BigInteger((v_k).Count))) {
        if ((_1_i) != (_0_x)) {
          if ((BasicArithmetic.__default.Abs(((v_k).Select(_0_x)) - ((v_k).Select(_1_i)))) <= ((e) * (((L).Select(_1_i)).Select(_0_x)))) {
            b = false;
            goto after_0;
          }
        }
        _1_i = (_1_i) + (BigInteger.One);
      continue_0: ;
      }
    after_0: ;
      return b;
    }
    public static BigInteger Classification(Dafny.ISequence<Dafny.BigRational> v) {
      return Lipschitz.__default.ArgMax(v);
    }
    public static BigInteger ArgMax(Dafny.ISequence<Dafny.BigRational> xs) {
      return (Lipschitz.__default.ArgMaxHelper(xs)).dtor__0;
    }
    public static _System._ITuple2<BigInteger, Dafny.BigRational> ArgMaxHelper(Dafny.ISequence<Dafny.BigRational> xs) {
      if (((new BigInteger((xs).Count)) == (BigInteger.One)) || (((Lipschitz.__default.ArgMaxHelper((xs).Subsequence(BigInteger.Zero, (new BigInteger((xs).Count)) - (BigInteger.One)))).dtor__1) < ((xs).Select((new BigInteger((xs).Count)) - (BigInteger.One))))) {
        return _System.Tuple2<BigInteger, Dafny.BigRational>.create((new BigInteger((xs).Count)) - (BigInteger.One), (xs).Select((new BigInteger((xs).Count)) - (BigInteger.One)));
      } else {
        return Lipschitz.__default.ArgMaxHelper((xs).Subsequence(BigInteger.Zero, (new BigInteger((xs).Count)) - (BigInteger.One)));
      }
    }
    public static Dafny.ISequence<Dafny.ISequence<Dafny.BigRational>> GenMarginLipBounds(Lipschitz.LipschitzBounds L, Dafny.ISequence<Dafny.ISequence<Dafny.ISequence<Dafny.BigRational>>> n, Dafny.ISequence<Dafny.BigRational> s)
    {
      Dafny.ISequence<Dafny.ISequence<Dafny.BigRational>> r = Dafny.Sequence<Dafny.ISequence<Dafny.BigRational>>.Empty;
      r = Dafny.Sequence<Dafny.ISequence<Dafny.BigRational>>.FromElements();
      BigInteger _0_i;
      _0_i = BigInteger.Zero;
      while ((_0_i) < (new BigInteger(((n).Select((new BigInteger((n).Count)) - (BigInteger.One))).Count))) {
        BigInteger _1_k;
        _1_k = BigInteger.Zero;
        Dafny.ISequence<Dafny.BigRational> _2_bound;
        _2_bound = Dafny.Sequence<Dafny.BigRational>.FromElements();
        while ((_1_k) < (new BigInteger(((n).Select((new BigInteger((n).Count)) - (BigInteger.One))).Count))) {
          if ((_1_k) == (_0_i)) {
            _2_bound = Dafny.Sequence<Dafny.BigRational>.Concat(_2_bound, Dafny.Sequence<Dafny.BigRational>.FromElements(new Dafny.BigRational(BigInteger.Parse("0"), BigInteger.One)));
          } else {
            Dafny.BigRational _3_b;
            Dafny.BigRational _out0;
            _out0 = Lipschitz.__default.GenMarginLipBound(L, n, _0_i, _1_k, s);
            _3_b = _out0;
            _2_bound = Dafny.Sequence<Dafny.BigRational>.Concat(_2_bound, Dafny.Sequence<Dafny.BigRational>.FromElements(_3_b));
          }
          _1_k = (_1_k) + (BigInteger.One);
        }
        r = Dafny.Sequence<Dafny.ISequence<Dafny.BigRational>>.Concat(r, Dafny.Sequence<Dafny.ISequence<Dafny.BigRational>>.FromElements(_2_bound));
        _0_i = (_0_i) + (BigInteger.One);
      }
      return r;
    }
    public static Dafny.ISequence<Dafny.BigRational> GenLipBounds(Lipschitz.LipschitzBounds L, Dafny.ISequence<Dafny.ISequence<Dafny.ISequence<Dafny.BigRational>>> n, Dafny.ISequence<Dafny.BigRational> s)
    {
      Dafny.ISequence<Dafny.BigRational> r = Dafny.Sequence<Dafny.BigRational>.Empty;
      r = Dafny.Sequence<Dafny.BigRational>.FromElements();
      BigInteger _0_i;
      _0_i = BigInteger.Zero;
      while ((_0_i) < (new BigInteger(((n).Select((new BigInteger((n).Count)) - (BigInteger.One))).Count))) {
        Dafny.BigRational _1_bound;
        Dafny.BigRational _out0;
        _out0 = Lipschitz.__default.GenLipBound(L, n, _0_i, s);
        _1_bound = _out0;
        r = Dafny.Sequence<Dafny.BigRational>.Concat(r, Dafny.Sequence<Dafny.BigRational>.FromElements(_1_bound));
        _0_i = (_0_i) + (BigInteger.One);
      }
      return r;
    }
    public static Dafny.BigRational GenLipBound(Lipschitz.LipschitzBounds L, Dafny.ISequence<Dafny.ISequence<Dafny.ISequence<Dafny.BigRational>>> n, BigInteger l, Dafny.ISequence<Dafny.BigRational> s)
    {
      Dafny.BigRational r = Dafny.BigRational.ZERO;
      Dafny.ISequence<Dafny.ISequence<Dafny.BigRational>> _0_trimmedLayer;
      _0_trimmedLayer = Dafny.Sequence<Dafny.ISequence<Dafny.BigRational>>.FromElements(((n).Select((new BigInteger((n).Count)) - (BigInteger.One))).Select(l));
      Dafny.BigRational _1_trimmedSpecNorm;
      Dafny.BigRational _out0;
      _out0 = (L).GramIterationSimple(_0_trimmedLayer);
      _1_trimmedSpecNorm = _out0;
      Dafny.ISequence<Dafny.ISequence<Dafny.ISequence<Dafny.BigRational>>> _2_n_k;
      _2_n_k = Dafny.Sequence<Dafny.ISequence<Dafny.ISequence<Dafny.BigRational>>>.Concat((n).Take((new BigInteger((n).Count)) - (BigInteger.One)), Dafny.Sequence<Dafny.ISequence<Dafny.ISequence<Dafny.BigRational>>>.FromElements(_0_trimmedLayer));
      Dafny.ISequence<Dafny.BigRational> _3_s_k;
      _3_s_k = Dafny.Sequence<Dafny.BigRational>.Concat((s).Take((new BigInteger((s).Count)) - (BigInteger.One)), Dafny.Sequence<Dafny.BigRational>.FromElements(_1_trimmedSpecNorm));
      r = Lipschitz.__default.Product(_3_s_k);
      return r;
    }
    public static Dafny.BigRational GenMarginLipBound(Lipschitz.LipschitzBounds L, Dafny.ISequence<Dafny.ISequence<Dafny.ISequence<Dafny.BigRational>>> n, BigInteger l, BigInteger k, Dafny.ISequence<Dafny.BigRational> s)
    {
      Dafny.BigRational r = Dafny.BigRational.ZERO;
      Dafny.ISequence<Dafny.BigRational> _0_vl;
      _0_vl = ((n).Select((new BigInteger((n).Count)) - (BigInteger.One))).Select(l);
      Dafny.ISequence<Dafny.BigRational> _1_vk;
      _1_vk = ((n).Select((new BigInteger((n).Count)) - (BigInteger.One))).Select(k);
      Dafny.ISequence<Dafny.BigRational> _2_trimmedLayerV;
      _2_trimmedLayerV = Lipschitz.__default.Minus(_0_vl, _1_vk);
      Dafny.ISequence<Dafny.ISequence<Dafny.BigRational>> _3_trimmedLayer;
      _3_trimmedLayer = Dafny.Sequence<Dafny.ISequence<Dafny.BigRational>>.FromElements(_2_trimmedLayerV);
      Dafny.BigRational _4_trimmedSpecNorm;
      Dafny.BigRational _out0;
      _out0 = Lipschitz.__default.L2UpperBound(_2_trimmedLayerV);
      _4_trimmedSpecNorm = _out0;
      Dafny.ISequence<Dafny.ISequence<Dafny.ISequence<Dafny.BigRational>>> _5_n_k;
      _5_n_k = Dafny.Sequence<Dafny.ISequence<Dafny.ISequence<Dafny.BigRational>>>.Concat((n).Take((new BigInteger((n).Count)) - (BigInteger.One)), Dafny.Sequence<Dafny.ISequence<Dafny.ISequence<Dafny.BigRational>>>.FromElements(_3_trimmedLayer));
      Dafny.ISequence<Dafny.BigRational> _6_s_k;
      _6_s_k = Dafny.Sequence<Dafny.BigRational>.Concat((s).Take((new BigInteger((s).Count)) - (BigInteger.One)), Dafny.Sequence<Dafny.BigRational>.FromElements(_4_trimmedSpecNorm));
      r = Lipschitz.__default.Product(_6_s_k);
      return r;
    }
  }

  public partial class Vector {
    private static readonly Dafny.ISequence<Dafny.BigRational> Witness = Dafny.Sequence<Dafny.BigRational>.FromElements(new Dafny.BigRational(BigInteger.Parse("0"), BigInteger.One));
    public static Dafny.ISequence<Dafny.BigRational> Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<Dafny.ISequence<Dafny.BigRational>> _TYPE = new Dafny.TypeDescriptor<Dafny.ISequence<Dafny.BigRational>>(Lipschitz.Vector.Default());
    public static Dafny.TypeDescriptor<Dafny.ISequence<Dafny.BigRational>> _TypeDescriptor() {
      return _TYPE;
    }
    public static bool _Is(Dafny.ISequence<Dafny.BigRational> __source) {
      Dafny.ISequence<Dafny.BigRational> _0_v = __source;
      return (new BigInteger((_0_v).Count)).Sign == 1;
    }
  }

  public partial class Matrix {
    private static readonly Dafny.ISequence<Dafny.ISequence<Dafny.BigRational>> Witness = Dafny.Sequence<Dafny.ISequence<Dafny.BigRational>>.FromElements(Lipschitz.__default.NonEmptyVector());
    public static Dafny.ISequence<Dafny.ISequence<Dafny.BigRational>> Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<Dafny.ISequence<Dafny.ISequence<Dafny.BigRational>>> _TYPE = new Dafny.TypeDescriptor<Dafny.ISequence<Dafny.ISequence<Dafny.BigRational>>>(Lipschitz.Matrix.Default());
    public static Dafny.TypeDescriptor<Dafny.ISequence<Dafny.ISequence<Dafny.BigRational>>> _TypeDescriptor() {
      return _TYPE;
    }
    public static bool _Is(Dafny.ISequence<Dafny.ISequence<Dafny.BigRational>> __source) {
      Dafny.ISequence<Dafny.ISequence<Dafny.BigRational>> _1_m = __source;
      return (((new BigInteger((_1_m).Count)).Sign == 1) && ((new BigInteger(((_1_m).Select(BigInteger.Zero)).Count)).Sign == 1)) && (Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.ISequence<Dafny.BigRational>>, bool>>((_2_m) => Dafny.Helpers.Quantifier<BigInteger>(Dafny.Helpers.IntegerRange(BigInteger.Zero, new BigInteger((_2_m).Count)), true, (((_forall_var_0) => {
        BigInteger _3_i = (BigInteger)_forall_var_0;
        return Dafny.Helpers.Quantifier<BigInteger>(Dafny.Helpers.IntegerRange(BigInteger.Zero, new BigInteger((_2_m).Count)), true, (((_forall_var_1) => {
          BigInteger _4_j = (BigInteger)_forall_var_1;
          return !((((_3_i).Sign != -1) && ((_3_i) < (new BigInteger((_2_m).Count)))) && (((_4_j).Sign != -1) && ((_4_j) < (new BigInteger((_2_m).Count))))) || ((new BigInteger(((_2_m).Select(_3_i)).Count)) == (new BigInteger(((_2_m).Select(_4_j)).Count)));
        })));
      }))))(_1_m));
    }
  }

  public partial class NeuralNetwork {
    private static readonly Dafny.ISequence<Dafny.ISequence<Dafny.ISequence<Dafny.BigRational>>> Witness = Dafny.Sequence<Dafny.ISequence<Dafny.ISequence<Dafny.BigRational>>>.FromElements(Lipschitz.__default.NonEmptyMatrix());
    public static Dafny.ISequence<Dafny.ISequence<Dafny.ISequence<Dafny.BigRational>>> Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<Dafny.ISequence<Dafny.ISequence<Dafny.ISequence<Dafny.BigRational>>>> _TYPE = new Dafny.TypeDescriptor<Dafny.ISequence<Dafny.ISequence<Dafny.ISequence<Dafny.BigRational>>>>(Lipschitz.NeuralNetwork.Default());
    public static Dafny.TypeDescriptor<Dafny.ISequence<Dafny.ISequence<Dafny.ISequence<Dafny.BigRational>>>> _TypeDescriptor() {
      return _TYPE;
    }
    public static bool _Is(Dafny.ISequence<Dafny.ISequence<Dafny.ISequence<Dafny.BigRational>>> __source) {
      Dafny.ISequence<Dafny.ISequence<Dafny.ISequence<Dafny.BigRational>>> _5_n = __source;
      return ((new BigInteger((_5_n).Count)).Sign == 1) && (Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.ISequence<Dafny.ISequence<Dafny.BigRational>>>, bool>>((_6_n) => Dafny.Helpers.Quantifier<BigInteger>(Dafny.Helpers.IntegerRange(BigInteger.Zero, (new BigInteger((_6_n).Count)) - (BigInteger.One)), true, (((_forall_var_2) => {
        BigInteger _7_i = (BigInteger)_forall_var_2;
        return !(((_7_i).Sign != -1) && ((_7_i) < ((new BigInteger((_6_n).Count)) - (BigInteger.One)))) || ((new BigInteger(((_6_n).Select(_7_i)).Count)) == (new BigInteger((((_6_n).Select((_7_i) + (BigInteger.One))).Select(BigInteger.Zero)).Count)));
      }))))(_5_n));
    }
  }

  public partial class LipschitzBounds {
    public LipschitzBounds() {
      this.GRAM__ITERATIONS = BigInteger.Zero;
    }
    public BigInteger GRAM__ITERATIONS {get; set;}
    public void __ctor(BigInteger G)
    {
      (this).GRAM__ITERATIONS = G;
    }
    public Dafny.BigRational GramIterationSimple(Dafny.ISequence<Dafny.ISequence<Dafny.BigRational>> G)
    {
      Dafny.BigRational s = Dafny.BigRational.ZERO;
      BigInteger _0_i;
      _0_i = BigInteger.Zero;
      Dafny.ISequence<Dafny.ISequence<Dafny.BigRational>> _1_G_k;
      _1_G_k = G;
      while ((_0_i) != (this.GRAM__ITERATIONS)) {
        if (BasicArithmetic.__default.DEBUG) {
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("{ \"debug_msg\": \"Gram iteration for matrix of size ")));
          Dafny.Helpers.Print((new BigInteger((G).Count)));
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("x")));
          Dafny.Helpers.Print((new BigInteger(((G).Select(BigInteger.Zero)).Count)));
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(". Iteration ")));
          Dafny.Helpers.Print(((_0_i) + (BigInteger.One)));
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(" of ")));
          Dafny.Helpers.Print((this.GRAM__ITERATIONS));
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("\" },\n")));
        }
        if (BasicArithmetic.__default.DEBUG) {
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("{ \"debug_msg\": \"Gram iteration calling Transpose...\" },\n")));
        }
        Dafny.ISequence<Dafny.ISequence<Dafny.BigRational>> _2_GT;
        _2_GT = Lipschitz.__default.Transpose(_1_G_k);
        if (BasicArithmetic.__default.DEBUG) {
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("{ \"debug_msg\": \"Gram iteration Transpose done; calling MM...\" },\n")));
        }
        _1_G_k = Lipschitz.__default.MM(_2_GT, _1_G_k);
        if (BasicArithmetic.__default.DEBUG) {
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("{ \"debug_msg\": \"Gram iteration calling MM done.\" },\n")));
        }
        _0_i = (_0_i) + (BigInteger.One);
      }
      if (BasicArithmetic.__default.DEBUG) {
        Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("{ \"debug_msg\": \"Gram iteration done iterating\" },\n")));
      }
      if (BasicArithmetic.__default.DEBUG) {
        Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("{ \"debug_msg\": \"Gram iteration computing frobenius norm upper bound...\" },\n")));
      }
      Dafny.BigRational _out0;
      _out0 = Lipschitz.__default.FrobeniusNormUpperBound(_1_G_k);
      s = _out0;
      if (BasicArithmetic.__default.DEBUG) {
        Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("{ \"debug_msg\": \"Gram iteration computing square root upper bound...\" },\n")));
      }
      Dafny.BigRational _out1;
      _out1 = BasicArithmetic.__default.Power2RootUpperBound(s, this.GRAM__ITERATIONS);
      s = _out1;
      if (BasicArithmetic.__default.DEBUG) {
        Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("{ \"debug_msg\": \"Gram iteration done\" },\n")));
      }
      return s;
    }
  }
} // end of namespace Lipschitz
namespace MainModule {

  public partial class __default {
    public static void _Main(Dafny.ISequence<Dafny.ISequence<char>> args)
    {
      if ((new BigInteger((args).Count)) != (new BigInteger(3))) {
        Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("Usage: main <neural_network_input.txt> <GRAM_ITERATIONS>\n")));
        Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("Usage: main <neural_network_input.txt> <lipshitz_bounds_input.txt>\n")));
        return ;
      }
      Dafny.ISequence<char> _0_neuralNetStr;
      Dafny.ISequence<char> _out0;
      _out0 = MainModule.__default.ReadFromFile((args).Select(BigInteger.One));
      _0_neuralNetStr = _out0;
      _System._ITuple2<bool, Dafny.ISequence<Dafny.ISequence<Dafny.ISequence<Dafny.BigRational>>>> _1_maybeNeuralNet;
      _System._ITuple2<bool, Dafny.ISequence<Dafny.ISequence<Dafny.ISequence<Dafny.BigRational>>>> _out1;
      _out1 = MainModule.__default.ParseNeuralNet(_0_neuralNetStr);
      _1_maybeNeuralNet = _out1;
      if (!((_1_maybeNeuralNet).dtor__0)) {
        throw new Dafny.HaltException("main.dfy(25,4): " + Dafny.Sequence<char>.FromString("Failed to parse neural network."));}
      Dafny.ISequence<Dafny.ISequence<Dafny.ISequence<Dafny.BigRational>>> _2_neuralNet;
      _2_neuralNet = (_1_maybeNeuralNet).dtor__1;
      Dafny.ISequence<Dafny.ISequence<Dafny.BigRational>> _3_lipBounds = Dafny.Sequence<Dafny.ISequence<Dafny.BigRational>>.Empty;
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("[\n")));
      if (StringUtils.__default.IsInt((args).Select(new BigInteger(2)))) {
        BigInteger _4_GRAM__ITERATIONS;
        BigInteger _out2;
        _out2 = StringUtils.__default.ParseInt((args).Select(new BigInteger(2)));
        _4_GRAM__ITERATIONS = _out2;
        if ((_4_GRAM__ITERATIONS).Sign != 1) {
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("<GRAM_ITERATIONS> should be positive")));
          return ;
        }
        Lipschitz.LipschitzBounds _5_L;
        Lipschitz.LipschitzBounds _nw0 = new Lipschitz.LipschitzBounds();
        _nw0.__ctor(_4_GRAM__ITERATIONS);
        _5_L = _nw0;
        Dafny.ISequence<Dafny.BigRational> _6_specNorms;
        Dafny.ISequence<Dafny.BigRational> _out3;
        _out3 = Lipschitz.__default.GenerateSpecNorms(_5_L, _2_neuralNet);
        _6_specNorms = _out3;
        Dafny.ISequence<Dafny.ISequence<Dafny.BigRational>> _out4;
        _out4 = Lipschitz.__default.GenMarginLipBounds(_5_L, _2_neuralNet, _6_specNorms);
        _3_lipBounds = _out4;
        Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("{\n")));
        Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("  \"lipschitz_bounds\": ")));
        Dafny.Helpers.Print((_3_lipBounds));
        Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(",\n")));
        Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("  \"GRAM_ITERATIONS\": ")));
        Dafny.Helpers.Print((_4_GRAM__ITERATIONS));
        Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(",\n")));
        Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("  \"provenance\": \"generated\"\n")));
        Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("}\n")));
      } else {
        Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("Reading margin lipschitz bounds from a file not (currently) supported\n")));
        return ;
      }
      Dafny.ISequence<char> _7_inputStr;
      Dafny.ISequence<char> _out5;
      _out5 = MainModule.__default.ReadFromFile(Dafny.Sequence<char>.FromString("/dev/stdin"));
      _7_inputStr = _out5;
      Dafny.ISequence<Dafny.ISequence<char>> _8_lines;
      Dafny.ISequence<Dafny.ISequence<char>> _out6;
      _out6 = StringUtils.__default.Split(_7_inputStr, '\n');
      _8_lines = _out6;
      if ((new BigInteger((_8_lines).Count)).Sign != 1) {
        return ;
      }
      BigInteger _9_l;
      _9_l = BigInteger.Zero;
      while ((_9_l) < (new BigInteger((_8_lines).Count))) {
        Dafny.ISequence<char> _10_line;
        _10_line = (_8_lines).Select(_9_l);
        _9_l = (_9_l) + (BigInteger.One);
        Dafny.ISequence<Dafny.ISequence<char>> _11_inputSeq;
        Dafny.ISequence<Dafny.ISequence<char>> _out7;
        _out7 = StringUtils.__default.Split(_10_line, ' ');
        _11_inputSeq = _out7;
        if ((new BigInteger((_11_inputSeq).Count)) != (new BigInteger(2))) {
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("]\n")));
          return ;
        }
        if (((_11_inputSeq).Select(BigInteger.Zero)).Equals(Dafny.Sequence<char>.FromString(""))) {
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("]\n")));
          return ;
        }
        Dafny.ISequence<Dafny.ISequence<char>> _12_realsStr;
        Dafny.ISequence<Dafny.ISequence<char>> _out8;
        _out8 = StringUtils.__default.Split((_11_inputSeq).Select(BigInteger.Zero), ',');
        _12_realsStr = _out8;
        bool _13_areReals;
        bool _out9;
        _out9 = MainModule.__default.AreReals(_12_realsStr);
        _13_areReals = _out9;
        if (!(_13_areReals)) {
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("Error: The given output vector contained non-real values.\n")));
          goto continue_0;
        }
        Dafny.ISequence<Dafny.BigRational> _14_outputVector;
        Dafny.ISequence<Dafny.BigRational> _out10;
        _out10 = MainModule.__default.ParseReals(_12_realsStr);
        _14_outputVector = _out10;
        if (((_11_inputSeq).Select(BigInteger.One)).Equals(Dafny.Sequence<char>.FromString(""))) {
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("Error: The given error margin was found to be empty.\n")));
          goto continue_0;
        }
        bool _15_isReal;
        _15_isReal = StringUtils.__default.IsReal((_11_inputSeq).Select(BigInteger.One));
        if (!(_15_isReal)) {
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("Error: The given error margin is not of type real.\n")));
          goto continue_0;
        }
        Dafny.BigRational _16_errorMargin;
        Dafny.BigRational _out11;
        _out11 = StringUtils.__default.ParseReal((_11_inputSeq).Select(BigInteger.One));
        _16_errorMargin = _out11;
        if ((new BigInteger((_14_outputVector).Count)) != (new BigInteger((_3_lipBounds).Count))) {
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("Error: Expected a vector of size ")));
          Dafny.Helpers.Print((new BigInteger((_3_lipBounds).Count)));
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(", but got ")));
          Dafny.Helpers.Print((new BigInteger((_14_outputVector).Count)));
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(".\n")));
          goto continue_0;
        }
        bool _17_robust;
        bool _out12;
        _out12 = Lipschitz.__default.Certify(_14_outputVector, _16_errorMargin, _3_lipBounds);
        _17_robust = _out12;
        Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(",\n")));
        Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("{\n")));
        Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("\"output\": ")));
        Dafny.Helpers.Print((_14_outputVector));
        Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(",\n")));
        Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("\"radius\": ")));
        Dafny.Helpers.Print((_16_errorMargin));
        Dafny.Helpers.Print((Dafny.Sequence<char>.FromString(",\n")));
        Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("\"certified\": ")));
        Dafny.Helpers.Print((_17_robust));
        Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("\n")));
        Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("}\n")));
      continue_0: ;
      }
    after_0: ;
      Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("]\n")));
    }
    public static _System._ITuple2<bool, Dafny.ISequence<Dafny.ISequence<Dafny.ISequence<Dafny.BigRational>>>> ParseNeuralNet(Dafny.ISequence<char> xs)
    {
      _System._ITuple2<bool, Dafny.ISequence<Dafny.ISequence<Dafny.ISequence<Dafny.BigRational>>>> t = _System.Tuple2<bool, Dafny.ISequence<Dafny.ISequence<Dafny.ISequence<Dafny.BigRational>>>>.Default(false, Lipschitz.NeuralNetwork.Default());
      Dafny.ISequence<char> _0_err;
      _0_err = Dafny.Sequence<char>.FromString("");
      Dafny.ISequence<Dafny.ISequence<Dafny.ISequence<Dafny.BigRational>>> _1_matrices;
      _1_matrices = Dafny.Sequence<Dafny.ISequence<Dafny.ISequence<Dafny.BigRational>>>.FromElements();
      BigInteger _2_i;
      _2_i = BigInteger.Zero;
      while ((_2_i) < (new BigInteger((xs).Count))) {
        if (((_2_i) >= ((new BigInteger((xs).Count)) - (BigInteger.One))) || (!((xs).Subsequence(_2_i, (_2_i) + (new BigInteger(2)))).Equals(Dafny.Sequence<char>.FromString("[[")))) {
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("One")));
          t = _System.Tuple2<bool, Dafny.ISequence<Dafny.ISequence<Dafny.ISequence<Dafny.BigRational>>>>.create(false, Dafny.Sequence<Dafny.ISequence<Dafny.ISequence<Dafny.BigRational>>>.FromElements(Dafny.Sequence<Dafny.ISequence<Dafny.BigRational>>.FromElements(Dafny.Sequence<Dafny.BigRational>.FromElements(new Dafny.BigRational(BigInteger.Parse("0"), BigInteger.One)))));
          return t;
        }
        BigInteger _3_j;
        _3_j = (_2_i) + (new BigInteger(2));
        while (!((xs).Subsequence((_3_j) - (new BigInteger(2)), _3_j)).Equals(Dafny.Sequence<char>.FromString("]]"))) {
          if ((_3_j) >= (new BigInteger((xs).Count))) {
            Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("Two")));
            t = _System.Tuple2<bool, Dafny.ISequence<Dafny.ISequence<Dafny.ISequence<Dafny.BigRational>>>>.create(false, Dafny.Sequence<Dafny.ISequence<Dafny.ISequence<Dafny.BigRational>>>.FromElements(Dafny.Sequence<Dafny.ISequence<Dafny.BigRational>>.FromElements(Dafny.Sequence<Dafny.BigRational>.FromElements(new Dafny.BigRational(BigInteger.Parse("0"), BigInteger.One)))));
            return t;
          }
          _3_j = (_3_j) + (BigInteger.One);
        }
        Dafny.ISequence<char> _4_ys;
        _4_ys = (xs).Subsequence((_2_i) + (BigInteger.One), (_3_j) - (BigInteger.One));
        BigInteger _5_k;
        _5_k = BigInteger.Zero;
        Dafny.ISequence<Dafny.ISequence<Dafny.BigRational>> _6_vectors;
        _6_vectors = Dafny.Sequence<Dafny.ISequence<Dafny.BigRational>>.FromElements();
        while ((_5_k) < (new BigInteger((_4_ys).Count))) {
          if (((_4_ys).Select(_5_k)) != ('[')) {
            Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("Three")));
            t = _System.Tuple2<bool, Dafny.ISequence<Dafny.ISequence<Dafny.ISequence<Dafny.BigRational>>>>.create(false, Dafny.Sequence<Dafny.ISequence<Dafny.ISequence<Dafny.BigRational>>>.FromElements(Dafny.Sequence<Dafny.ISequence<Dafny.BigRational>>.FromElements(Dafny.Sequence<Dafny.BigRational>.FromElements(new Dafny.BigRational(BigInteger.Parse("0"), BigInteger.One)))));
            return t;
          }
          BigInteger _7_l;
          _7_l = _5_k;
          while (((_4_ys).Select(_7_l)) != (']')) {
            if (((_7_l) + (BigInteger.One)) >= (new BigInteger((_4_ys).Count))) {
              Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("Four")));
              t = _System.Tuple2<bool, Dafny.ISequence<Dafny.ISequence<Dafny.ISequence<Dafny.BigRational>>>>.create(false, Dafny.Sequence<Dafny.ISequence<Dafny.ISequence<Dafny.BigRational>>>.FromElements(Dafny.Sequence<Dafny.ISequence<Dafny.BigRational>>.FromElements(Dafny.Sequence<Dafny.BigRational>.FromElements(new Dafny.BigRational(BigInteger.Parse("0"), BigInteger.One)))));
              return t;
            }
            _7_l = (_7_l) + (BigInteger.One);
          }
          Dafny.ISequence<char> _8_zs;
          _8_zs = (_4_ys).Subsequence((_5_k) + (BigInteger.One), _7_l);
          Dafny.ISequence<Dafny.ISequence<char>> _9_realsStr;
          Dafny.ISequence<Dafny.ISequence<char>> _out0;
          _out0 = StringUtils.__default.Split(_8_zs, ',');
          _9_realsStr = _out0;
          bool _10_areReals;
          bool _out1;
          _out1 = MainModule.__default.AreReals(_9_realsStr);
          _10_areReals = _out1;
          if (!(_10_areReals)) {
            Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("Five\n")));
            t = _System.Tuple2<bool, Dafny.ISequence<Dafny.ISequence<Dafny.ISequence<Dafny.BigRational>>>>.create(false, Dafny.Sequence<Dafny.ISequence<Dafny.ISequence<Dafny.BigRational>>>.FromElements(Dafny.Sequence<Dafny.ISequence<Dafny.BigRational>>.FromElements(Dafny.Sequence<Dafny.BigRational>.FromElements(new Dafny.BigRational(BigInteger.Parse("0"), BigInteger.One)))));
            return t;
          }
          Dafny.ISequence<Dafny.BigRational> _11_v;
          Dafny.ISequence<Dafny.BigRational> _out2;
          _out2 = MainModule.__default.ParseReals(_9_realsStr);
          _11_v = _out2;
          if ((new BigInteger((_11_v).Count)).Sign == 0) {
            t = _System.Tuple2<bool, Dafny.ISequence<Dafny.ISequence<Dafny.ISequence<Dafny.BigRational>>>>.create(false, Dafny.Sequence<Dafny.ISequence<Dafny.ISequence<Dafny.BigRational>>>.FromElements(Dafny.Sequence<Dafny.ISequence<Dafny.BigRational>>.FromElements(Dafny.Sequence<Dafny.BigRational>.FromElements(new Dafny.BigRational(BigInteger.Parse("0"), BigInteger.One)))));
            return t;
          }
          Dafny.ISequence<Dafny.BigRational> _12_v_k;
          _12_v_k = _11_v;
          _6_vectors = Dafny.Sequence<Dafny.ISequence<Dafny.BigRational>>.Concat(_6_vectors, Dafny.Sequence<Dafny.ISequence<Dafny.BigRational>>.FromElements(_12_v_k));
          _5_k = (_7_l) + (new BigInteger(2));
        }
        bool _13_matrixWellFormed;
        bool _out3;
        _out3 = MainModule.__default.IsMatrixWellFormed(_6_vectors);
        _13_matrixWellFormed = _out3;
        if (!(_13_matrixWellFormed)) {
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("Six")));
          t = _System.Tuple2<bool, Dafny.ISequence<Dafny.ISequence<Dafny.ISequence<Dafny.BigRational>>>>.create(false, Dafny.Sequence<Dafny.ISequence<Dafny.ISequence<Dafny.BigRational>>>.FromElements(Dafny.Sequence<Dafny.ISequence<Dafny.BigRational>>.FromElements(Dafny.Sequence<Dafny.BigRational>.FromElements(new Dafny.BigRational(BigInteger.Parse("0"), BigInteger.One)))));
          return t;
        }
        Dafny.ISequence<Dafny.ISequence<Dafny.BigRational>> _14_matrix;
        _14_matrix = _6_vectors;
        _1_matrices = Dafny.Sequence<Dafny.ISequence<Dafny.ISequence<Dafny.BigRational>>>.Concat(_1_matrices, Dafny.Sequence<Dafny.ISequence<Dafny.ISequence<Dafny.BigRational>>>.FromElements(Lipschitz.__default.Transpose(_14_matrix)));
        _2_i = (_3_j) + (BigInteger.One);
      }
      bool _15_neuralNetWellFormed;
      bool _out4;
      _out4 = MainModule.__default.IsNeuralNetWellFormed(_1_matrices);
      _15_neuralNetWellFormed = _out4;
      if (!(_15_neuralNetWellFormed)) {
        Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("Seven\n")));
        Dafny.Helpers.Print((new BigInteger((_1_matrices).Count)));
        Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("\n")));
        if ((new BigInteger((_1_matrices).Count)) == (new BigInteger(2))) {
          Dafny.Helpers.Print((new BigInteger(((_1_matrices).Select(BigInteger.Zero)).Count)));
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("\n")));
          if ((new BigInteger(((_1_matrices).Select(BigInteger.Zero)).Count)).Sign == 1) {
            Dafny.Helpers.Print((new BigInteger((((_1_matrices).Select(BigInteger.Zero)).Select(BigInteger.Zero)).Count)));
            Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("\n")));
          }
          Dafny.Helpers.Print((new BigInteger(((_1_matrices).Select(BigInteger.One)).Count)));
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("\n")));
          if ((new BigInteger(((_1_matrices).Select(BigInteger.One)).Count)).Sign == 1) {
            Dafny.Helpers.Print((new BigInteger((((_1_matrices).Select(BigInteger.One)).Select(BigInteger.Zero)).Count)));
            Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("\n")));
          }
        }
        t = _System.Tuple2<bool, Dafny.ISequence<Dafny.ISequence<Dafny.ISequence<Dafny.BigRational>>>>.create(false, Dafny.Sequence<Dafny.ISequence<Dafny.ISequence<Dafny.BigRational>>>.FromElements(Dafny.Sequence<Dafny.ISequence<Dafny.BigRational>>.FromElements(Dafny.Sequence<Dafny.BigRational>.FromElements(new Dafny.BigRational(BigInteger.Parse("0"), BigInteger.One)))));
        return t;
      }
      Dafny.ISequence<Dafny.ISequence<Dafny.ISequence<Dafny.BigRational>>> _16_neuralNet;
      _16_neuralNet = _1_matrices;
      t = _System.Tuple2<bool, Dafny.ISequence<Dafny.ISequence<Dafny.ISequence<Dafny.BigRational>>>>.create(true, _16_neuralNet);
      return t;
      return t;
    }
    public static bool IsNeuralNetWellFormed(Dafny.ISequence<Dafny.ISequence<Dafny.ISequence<Dafny.BigRational>>> n)
    {
      bool b = false;
      if ((new BigInteger((n).Count)).Sign == 0) {
        b = false;
        return b;
      }
      BigInteger _0_i;
      _0_i = BigInteger.Zero;
      while ((_0_i) < ((new BigInteger((n).Count)) - (BigInteger.One))) {
        if ((new BigInteger(((n).Select(_0_i)).Count)) != (new BigInteger((((n).Select((_0_i) + (BigInteger.One))).Select(BigInteger.Zero)).Count))) {
          b = false;
          return b;
        }
        _0_i = (_0_i) + (BigInteger.One);
      }
      b = true;
      return b;
      return b;
    }
    public static bool IsMatrixWellFormed(Dafny.ISequence<Dafny.ISequence<Dafny.BigRational>> m)
    {
      bool b = false;
      if (((new BigInteger((m).Count)).Sign == 0) || ((new BigInteger(((m).Select(BigInteger.Zero)).Count)).Sign == 0)) {
        b = false;
        return b;
      }
      BigInteger _0_size;
      _0_size = new BigInteger(((m).Select(BigInteger.Zero)).Count);
      BigInteger _1_i;
      _1_i = BigInteger.One;
      while ((_1_i) < (new BigInteger((m).Count))) {
        if ((new BigInteger(((m).Select(_1_i)).Count)) != (_0_size)) {
          b = false;
          return b;
        }
        _1_i = (_1_i) + (BigInteger.One);
      }
      b = true;
      return b;
      return b;
    }
    public static bool AreReals(Dafny.ISequence<Dafny.ISequence<char>> realsStr)
    {
      bool b = false;
      BigInteger _hi0 = new BigInteger((realsStr).Count);
      for (BigInteger _0_i = BigInteger.Zero; _0_i < _hi0; _0_i++) {
        bool _1_isReal;
        _1_isReal = StringUtils.__default.IsReal((realsStr).Select(_0_i));
        if (!(_1_isReal)) {
          Dafny.Helpers.Print(((realsStr).Select(_0_i)));
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("\n")));
          b = false;
          return b;
        }
      }
      b = true;
      return b;
      return b;
    }
    public static Dafny.ISequence<Dafny.BigRational> ParseReals(Dafny.ISequence<Dafny.ISequence<char>> realsStr)
    {
      Dafny.ISequence<Dafny.BigRational> reals = Dafny.Sequence<Dafny.BigRational>.Empty;
      reals = Dafny.Sequence<Dafny.BigRational>.FromElements();
      BigInteger _hi0 = new BigInteger((realsStr).Count);
      for (BigInteger _0_i = BigInteger.Zero; _0_i < _hi0; _0_i++) {
        Dafny.BigRational _1_r;
        Dafny.BigRational _out0;
        _out0 = StringUtils.__default.ParseReal((realsStr).Select(_0_i));
        _1_r = _out0;
        reals = Dafny.Sequence<Dafny.BigRational>.Concat(reals, Dafny.Sequence<Dafny.BigRational>.FromElements(_1_r));
      }
      return reals;
    }
    public static Dafny.ISequence<char> ReadFromFile(Dafny.ISequence<char> filename)
    {
      Dafny.ISequence<char> str = Dafny.Sequence<char>.Empty;
      Wrappers._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>> _0_readResult;
      Wrappers._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>> _out0;
      _out0 = FileIO.__default.ReadBytesFromFile(filename);
      _0_readResult = _out0;
      if (!((_0_readResult).is_Success)) {
        throw new Dafny.HaltException("main.dfy(327,4): " + Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.FromString("Unexpected failure reading from "), filename), Dafny.Sequence<char>.FromString(": ")), (_0_readResult).dtor_error));}
      str = ((System.Func<Dafny.ISequence<char>>) (() => {
        BigInteger dim0 = new BigInteger(((_0_readResult).dtor_value).Count);
        var arr0 = new char[Dafny.Helpers.ToIntChecked(dim0, "array size exceeds memory limit")];
        for (int i0 = 0; i0 < dim0; i0++) {
          var _1_i = (BigInteger) i0;
          arr0[(int)(_1_i)] = (char)(((_0_readResult).dtor_value).Select(_1_i));
        }
        return Dafny.Sequence<char>.FromArray(arr0);
      }))();
      return str;
    }
  }
} // end of namespace MainModule
namespace _module {

} // end of namespace _module
class __CallToMain {
  public static void Main(string[] args) {
    Dafny.Helpers.WithHaltHandling(() => MainModule.__default._Main(Dafny.Sequence<Dafny.ISequence<char>>.FromMainArguments(args)));
  }
}
