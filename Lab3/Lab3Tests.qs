// QSD Lab 3 Tests
// Copyright 2023 The MITRE Corporation. All Rights Reserved.
//
// DO NOT MODIFY THIS FILE.

namespace Lab3 {

    open Microsoft.Quantum.Canon;
    open Microsoft.Quantum.Convert;
    open Microsoft.Quantum.Diagnostics;
    open Microsoft.Quantum.Intrinsic;
    open Microsoft.Quantum.Math;
    open Microsoft.Quantum.Random;

    operation GenerateRandomRotation () : Double[] {
        return [
            DrawRandomDouble(0.0, PI()),
            DrawRandomDouble(0.0, 2.0 * PI())
        ];
    }

    operation ApplyRotation (rotation : Double[], target: Qubit) : Unit
    is Adj + Ctl {
        Rx(rotation[0], target);
        Rz(rotation[1], target);
    }


    @Test("QuantumSimulator")
    operation Exercise1Test () : Unit {
        for i in 0 .. 4 {
            use qubits = Qubit[2];
            let rotations = [
                GenerateRandomRotation(),
                GenerateRandomRotation()
            ];

            ApplyRotation(rotations[0], qubits[0]);
            ApplyRotation(rotations[1], qubits[1]);

            Exercise1(qubits[0], qubits[1]);

            Adjoint ApplyRotation(rotations[0], qubits[1]);
            Adjoint ApplyRotation(rotations[1], qubits[0]);

            AssertAllZero(qubits);
        }
    }


    @Test("QuantumSimulator")
    operation Exercise2Test () : Unit {
        for numQubits in 3 .. 8 {
            use register = Qubit[numQubits];
            mutable rotations = [];
            for index in 0 .. numQubits - 1 {
                set rotations += [GenerateRandomRotation()];
                ApplyRotation(rotations[index], register[index]);
            }

            Exercise2(register);

            for index in 0 .. numQubits - 1 {
                Adjoint ApplyRotation(
                    rotations[numQubits - index - 1],
                    register[index]
                );
            }

            AssertAllZero(register);
        }
    }


    @Test("QuantumSimulator")
    operation Exercise3Test () : Unit {
        use qubits = Qubit[8];
        let registers = [
            [qubits[0], qubits[1]],
            [qubits[2], qubits[3]],
            [qubits[4], qubits[5]],
            [qubits[6], qubits[7]]
        ];

        Exercise3(registers);

        for register in registers {
            CNOT(register[0], register[1]);
            H(register[0]);
        }

        // now, register 0 should be |00>,
        //      register 1 should be |10>,
        //      register 2 should be |01>, and
        //      register 3 should be |11>
        X(registers[1][0]);
        X(registers[2][1]);
        X(registers[3][0]);
        X(registers[3][1]);

        AssertAllZero(qubits);
    }


    @Test("QuantumSimulator")
    operation Exercise4Test () : Unit {
        for numQubits in 2 .. 10 {
            use register = Qubit[numQubits];

            Exercise4(register);

            for index in 1 .. numQubits - 1 {
                CNOT(register[0], register[index]);
            }
            H(register[0]);

            AssertAllZero(register);
        }
    }


    @Test("QuantumSimulator")
    operation Exercise5Test () : Unit {
        use register = Qubit[4];

        Exercise5(register);

        Z(register[2]);
        X(register[3]);
        CNOT(register[2], register[3]);
        H(register[2]);
        X(register[1]);

        AssertAllZero(register);
    }


    @Test("QuantumSimulator")
    operation Exercise6Test () : Unit {
        use register = Qubit[2];

        Exercise6(register);

        Controlled H([register[0]], register[1]);
        H(register[0]);

        AssertAllZero(register);
    }

    @Test("QuantumSimulator")
    operation Exercise7Test () : Unit {
        use (register, target) = (Qubit[3], Qubit());

        Exercise7(register, target);

        ApplyToEach(X, register[0 .. 1]);
        Controlled X(register, target);
        ApplyToEach(X, register[0 .. 1]);
        ApplyToEach(H, register);

        AssertAllZero(register + [target]);
    }


    @Test("QuantumSimulator")
    operation Exercise8Test () : Unit {
        use register = Qubit[3];

        Exercise8(register);

        ApplyToEach(X, register[1 .. 2]);
        use ancilla = Qubit() {
            X(ancilla);
            Controlled Z(register, ancilla);
            X(ancilla);
        }
        ApplyToEach(X, register[1 .. 2]);
        CNOT(register[1], register[2]);
        Controlled H([register[0]], register[1]);
        H(register[0]);

        AssertAllZero(register);
    }


    @Test("QuantumSimulator")
    operation Challenge1Test () : Unit {
        use qubits = Qubit[2];

        Challenge1(qubits);

        X(qubits[0]);
        Controlled H([qubits[0]], qubits[1]);
        X(qubits[0]);

        let desiredProbability = 2.0 / 3.0;
        let angle = 2.0 * ArcCos(Sqrt(desiredProbability));
        Ry(-angle, qubits[0]);

        AssertAllZero(qubits);
    }


    @Test("QuantumSimulator")
    operation Challenge2Test () : Unit {
        use qubits = Qubit[3];

        Challenge2(qubits);

        X(qubits[0]);
        CNOT(qubits[0], qubits[2]);
        CNOT(qubits[1], qubits[2]);
        Controlled H([qubits[0]], qubits[1]);
        X(qubits[0]);

        let desiredProbability = 2.0 / 3.0;
        let angle = 2.0 * ArcCos(Sqrt(desiredProbability));
        Ry(-angle, qubits[0]);

        AssertAllZero(qubits);
    }


    @Test("QuantumSimulator")
    operation Challenge3Test () : Unit {
        use qubits = Qubit[3];

        Challenge3(qubits);

        X(qubits[2]);
        CNOT(qubits[2], qubits[1]);
        X(qubits[2]);
        Controlled H([qubits[2]], qubits[1]);
        H(qubits[2]);
        H(qubits[0]);
        X(qubits[0]);

        AssertAllZero(qubits);
    }


    @Test("QuantumSimulator")
    operation Challenge4Test () : Unit {
        use qubits = Qubit[3];

        Challenge4(qubits);

        CCNOT(qubits[2], qubits[0], qubits[1]);
        Controlled H([qubits[2]], qubits[1]);
        Controlled X([qubits[2]], qubits[1]);
        H(qubits[0]);
        X(qubits[2]);
        CNOT(qubits[2], qubits[0]);
        X(qubits[2]);
        H(qubits[2]);

        AssertAllZero(qubits);
    }
}