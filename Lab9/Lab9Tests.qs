// QSD Lab 9 Tests
// Copyright 2023 The MITRE Corporation. All Rights Reserved.
//
// DO NOT MODIFY THIS FILE.

namespace Lab9 {
    open Microsoft.Quantum.Arithmetic;
    open Microsoft.Quantum.Preparation;
    open Microsoft.Quantum.Math;
    open Microsoft.Quantum.Convert;
    open Microsoft.Quantum.Canon;
    open Microsoft.Quantum.Diagnostics;
    open Microsoft.Quantum.Intrinsic;
    open Microsoft.Quantum.Random;


    operation ReverseModExp(
        A : Int,
        B : Int,
        Input : Qubit[],
        Output : Qubit[]
    ) : Unit
    {
        let outputAsLE = LittleEndian(Output);
        let inputSize = Length(Input);

        for i in inputSize - 1..-1..0
        {
            let powerOfTwo = inputSize - 1 - i;	// n-i-1
            let powerOfGuess = 2 ^ powerOfTwo;	// 2^(n-i-1)

            let constant = ExpModI(A, powerOfGuess, B);	// c = A^(2^(n-i-1)) mod B
            Controlled Adjoint MultiplyByModularInteger([Input[i]],	// |O> = |O> * c mod B
                (constant, B, outputAsLE));
        }

        X(Output[Length(Output) - 1]);
    }


    operation RunModExpTest(
        Guess : Int,
        NumberToFactor : Int
    ) : Unit
    {
        let outputSize = Ceiling(Lg(IntAsDouble(NumberToFactor + 1)));
        use (input, output) = (Qubit[outputSize * 2], Qubit[outputSize])
        {
            ApplyToEach(H, input);

            Exercise1_ModExp(Guess, NumberToFactor, input, output);
            ReverseModExp(Guess, NumberToFactor, input, output);

            ApplyToEach(H, input);

            AssertAllZero(input + output);
        }
    }


    operation RunSubroutineTest(
        Guess : Int,
        NumberToFactor : Int,
        Period : Int,
        Tolerance : Double
    ) : Bool
    {
        let (measurement, searchSpace) = Exercise2_FindApproxPeriod(NumberToFactor, Guess);
        Message("Measured 0, trying again...");
        if measurement == 0 {
            return false;
        }
        let scaledMeasurement = IntAsDouble(measurement) / IntAsDouble(searchSpace) * IntAsDouble(Period);
        let nearestMultiple = Round(scaledMeasurement);
        let delta = AbsD(scaledMeasurement - IntAsDouble(nearestMultiple));

        Message($"Measured {measurement}/{searchSpace} => {scaledMeasurement}, delta = {delta}");
        EqualityFactB(delta < Tolerance, true, $"QFT failed, your measurement was too far from one of the expected values. It could just be (very) bad luck, so consider trying again if you think you have the correct implementation.");
        return true;
    }


    @Test("QuantumSimulator")
    operation Exercise1ModExpTest() : Unit {

        RunModExpTest(5, 9);

        RunModExpTest(7, 15);

        //RunModExpTest(11, 21);
    }


    @Test("QuantumSimulator")
    operation Exercise2SubroutineTest() : Unit {
        for i in 0..2 {
            mutable validMeasure = false;
            for j in 0..9 {
                if not validMeasure {
                    set validMeasure = RunSubroutineTest(5, 9, 6, 0.046875);
                }
            }
            if not validMeasure {
                fail "Your implementation measured 0 too many times. If you think you have the correct implementation, please try again.";
            }

            set validMeasure = false;
            for j in 0..4 {
                if not validMeasure {
                    set validMeasure = RunSubroutineTest(7, 15, 4, 0.03125);
                }
            }
            if not validMeasure {
                fail "Your implementation measured 0 too many times. If you think you have the correct implementation, please try again.";
            }
        }
    }


    @Test("QuantumSimulator")
    function Exercise3ConvergentTest() : Unit {

        mutable tests = [
            // 5 mod 9
            (0, 256, 0, 1, 9),
            (43, 256, 1, 6, 9),
            (85, 256, 1, 3, 9),
            (128, 256, 1, 2, 9),
            (171, 256, 2, 3, 9),
            (213, 256, 5, 6, 9),

            // 7 mod 15
            (0, 256, 0, 1, 15),
            (64, 256, 1, 4, 15),
            (128, 256, 1, 2, 15),
            (192, 256, 3, 4, 15),

            // 11 mod 21
            (0, 512, 0, 1, 21),
            (85, 512, 1, 6, 21),
            (171, 512, 1, 3, 21),
            (256, 512, 1, 2, 21),
            (341, 512, 2, 3, 21),
            (427, 512, 5, 6, 21)
        ];

        for test in tests {
            let (testNumerator, testDenominator, trueNumerator, trueDenominator, threshold) = test;
            let (numerator, denominator) = Exercise3_FindPeriodCandidate(testNumerator, testDenominator, threshold);
            if denominator == 0 {
                fail "You returned a denominator of 0, which should not be possible.";
            }
            EqualityFactI(numerator, trueNumerator, $"You gave {numerator} / {denominator}, which doesn't match the expected convergent for {testNumerator} / {testDenominator}.");
            EqualityFactI(denominator, trueDenominator, $"You gave {numerator} / {denominator}, which doesn't match the expected convergent for {testNumerator} / {testDenominator}.");
        }

    }


    @Test("QuantumSimulator")
    operation Exercise4PeriodTest() : Unit {
        mutable period = Exercise4_FindPeriod(9, 5);
        EqualityFactI(period, 6, "Incorrect period found.");

        set period = Exercise4_FindPeriod(15, 7);
        EqualityFactI(period, 4, "Incorrect period found.");
    }


    @Test("QuantumSimulator")
    function Exercise5FactorTest() : Unit {

        EqualityFactI(Exercise5_FindFactor(9, 2, 6), -2, "Your function should have returned -2 because this period results in a factor of 1.");

        EqualityFactI(Exercise5_FindFactor(9, 4, 3), -1, "Your function should have returned -1 because this period is odd.");

        EqualityFactI(Exercise5_FindFactor(9, 7, 3), -1, "Your function should have returned -1 because this period is odd.");

        mutable factor = Exercise5_FindFactor(15, 2, 4);
        if (factor != 5 and factor != 3)
        {
            fail $"You returned an incorrect factor, expected 3 or 5 but got {factor}.";
        }

        set factor = Exercise5_FindFactor(15, 4, 2);
        if (factor != 5 and factor != 3)
        {
            fail $"You returned an incorrect factor, expected 3 or 5 but got {factor}.";
        }

        set factor = Exercise5_FindFactor(15, 7, 4);
        if (factor != 5 and factor != 3)
        {
            fail $"You returned an incorrect factor, expected 3 or 5 but got {factor}.";
        }

        set factor = Exercise5_FindFactor(15, 8, 4);
        if (factor != 5 and factor != 3)
        {
            fail $"You returned an incorrect factor, expected 3 or 5 but got {factor}.";
        }

        set factor = Exercise5_FindFactor(15, 11, 2);
        if (factor != 5 and factor != 3)
        {
            fail $"You returned an incorrect factor, expected 3 or 5 but got {factor}.";
        }

        set factor = Exercise5_FindFactor(15, 13, 4);
        if (factor != 5 and factor != 3)
        {
            fail $"You returned an incorrect factor, expected 3 or 5 but got {factor}.";
        }

        set factor = Exercise5_FindFactor(21, 2, 6);
        if (factor != 7 and factor != 3)
        {
            fail $"You returned an incorrect factor, expected 3 or 7 but got {factor}.";
        }

        EqualityFactI(Exercise5_FindFactor(21, 4, 3), -1, "Your function should have returned -1 because this period is odd.");

        EqualityFactI(Exercise5_FindFactor(21, 5, 6), -2, "Your function should have returned -2 because this period results in a factor of 1.");

        set factor = Exercise5_FindFactor(21, 8, 2);
        if (factor != 7 and factor != 3)
        {
            fail $"You returned an incorrect factor, expected 3 or 7 but got {factor}.";
        }

        set factor = Exercise5_FindFactor(21, 10, 6);
        if (factor != 7 and factor != 3)
        {
            fail $"You returned an incorrect factor, expected 3 or 7 but got {factor}.";
        }

        set factor = Exercise5_FindFactor(21, 11, 6);
        if (factor != 7 and factor != 3)
        {
            fail $"You returned an incorrect factor, expected 3 or 7 but got {factor}.";
        }

        set factor = Exercise5_FindFactor(21, 13, 2);
        if (factor != 7 and factor != 3)
        {
            fail $"You returned an incorrect factor, expected 3 or 7 but got {factor}.";
        }

        EqualityFactI(Exercise5_FindFactor(21, 16, 3), -1, "Your function should have returned -1 because this period is odd.");

        EqualityFactI(Exercise5_FindFactor(21, 17, 6), -2, "Your function should have returned -2 because this period results in a factor of 1.");

        set factor = Exercise5_FindFactor(21, 19, 6);
        if (factor != 7 and factor != 3)
        {
            fail $"You returned an incorrect factor, expected 3 or 7 but got {factor}.";
        }

        EqualityFactI(Exercise5_FindFactor(21, 20, 2), -2, "Your function should have returned -2 because this period results in a factor of 1.");
    }
}
