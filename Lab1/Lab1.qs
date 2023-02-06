// Lab 1: Setting up the Development Environment
// Copyright 2023 The MITRE Corporation. All Rights Reserved.
//
// Due 1/30 at 6:00PM ET:
//  - Completed exercises and evidence of unit tests passing uploaded to GitHub.
//  - Link to your GitHub repo shared in your private Discord channel.
//
//
// --- First Time Setup Instructions ---
//
//  1. Install .NET 6.0 SDK: https://dotnet.microsoft.com/en-us/download
//  2. Install VS Code: https://code.visualstudio.com/Download
//  3. Install the Microsoft QDK for VS Code: https://marketplace.visualstudio.com/items?itemName=quantum.quantum-devkit-vscode
//  4. Open the "Lab1" folder in VS Code.
//  5. Open the terminal with Ctrl + `. Run the command "dotnet test". The tests
//     should fail.
//  6. Modify the code in this file so the unit tests pass. Do not modify the
//     tests.
//
// If the above instructions do not work for you, DON'T PANIC! Post in the #help
// channel on Discord, or use your private channel if you'd prefer.
//
//
// --- Recommended Extensions ---
//
//  - C#: https://marketplace.visualstudio.com/items?itemName=ms-dotnettools.csharp
//  - .NET Core Test Explorer: https://marketplace.visualstudio.com/items?itemName=formulahendry.dotnet-test-explorer
//
//
// --- Tips ---
//
//  - To target an individual test, use the --filter flag. For example,
//    "dotnet test --filter Exercise1".
//  - Don't forget to remove the fail statements!
//  - If your .csproj file gets messed up or you are having version issues, you
//    can create a new project and copy the assignment and unit tests over. See
//    https://learn.microsoft.com/en-us/azure/quantum/user-guide/testing-debugging?tabs=tabid-vscode#creating-a-test-project
//

namespace Lab1 {

    open Microsoft.Quantum.Canon;
    open Microsoft.Quantum.Convert;
    open Microsoft.Quantum.Intrinsic;

    /// # Summary
    /// In this exercise, you are given a single qubit which is in the |0>
    /// state. Your objective is to flip the qubit. Use the single-qubit
    /// quantum gates that Q# provides to transform it into the |1> state.
    ///
    /// # Input
    /// ## target
    /// The qubit you need to flip. It will be in the |0> state initially.
    ///
    /// # Remarks
    /// This will show you how to apply quantum gates to qubits in Q#.
    operation Exercise1 (target: Qubit) : Unit {
        X(target);
    }

    /// # Summary
    /// In this exercise, you are given two qubits. Both of them are in the |0>
    /// state. Using the single-qubit gates, turn them into the |+> state and
    /// |-> state respectively. Recall the |+> state is 1/√2(|0> + |1>) and the
    /// |-> state is 1/√2(|0> - |1>).
    ///
    /// # Input
    /// ## targetA
    /// Turn this qubit from |0> to |+>.
    ///
    /// ## targetB
    /// Turn this qubit from |0> to |->.
    ///
    /// # Remarks
    /// This should show you how to use single-qubit gates to put qubits into
    /// uniform quantum superpositions.
    operation Exercise2 (targetA : Qubit, targetB : Qubit) : Unit {
        H(targetA);
        X(targetB);
        H(targetB);
    }

}