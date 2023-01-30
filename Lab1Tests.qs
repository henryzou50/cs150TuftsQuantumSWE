// Lab 1 Tests
// Copyright 2023 The MITRE Corporation. All Rights Reserved.
//
// DO NOT MODIFY THIS FILE.
//

namespace Lab1 {

    open Microsoft.Quantum.Canon;
    open Microsoft.Quantum.Diagnostics;
    open Microsoft.Quantum.Intrinsic;


    @Test("QuantumSimulator")
    operation Exercise1Test () : Unit {
        use target = Qubit();

        Exercise1(target);

        X(target);

        AssertQubit(Zero, target);
    }


    @Test("QuantumSimulator")
    operation Exercise2Test () : Unit {
        use targets = Qubit[2];

        Exercise2(targets[0], targets[1]);

        H(targets[0]);
        H(targets[1]);
        X(targets[1]);

        AssertAllZero(targets);
    }

}
