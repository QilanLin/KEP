<table width=90% class="table_report_clear">
    <tr>
        <td width=150>Project supervisor:</td>
        <td>Mansour, Mohammad Ahmad Abdulaziz Ali</td>
    </tr>
    <tr>
        <td>Stage:</td>
        <td>BSc/MSci Year 3</td>
    </tr>
    <tr>
        <td>Project title:</td>
        <td>
            <b>
                <b>KEP Project:</b>
                Trust Me, I am a Verifier! (Or should you?) Proof Assistant Reliability and Testing - Mohammad - variant 3
            </b>
        </td>
    </tr>
    <tr>
        <td>Project description:</td>
        <td>
            <b>Note: For every KEP project, please note that you are not eligible if you have not applied through by the official form.</b>
</br></br>A proof assistant is a program that checks if a given mathematical proof is correct. Proof assistants are used in many applications, ranging from practical software verification, like verifying a linux Kernel [1], a C-compiler [2], or cryptographic software by Apple [3] and AWS [4], to more theoretical applications in mathematics, like confirming the correctness of the proof of FermatÃÂÃÂÃÂÃÂs Last Theorem [5]. In software verification, a proof assistant is used to check proofs that a given program behaves exactly as intended ÃÂÃÂÃÂÃÂ no bugs, no surprise features, no unexpected behaviour. Proof assistants depend on a multitude of pieces of software that are integrated in complex architectures, e.g. compilers, external solvers, etc. Although the core of a proof assistant might not have bugs, the surrounding software might have bugs that affect the usability, reliability, or usefulness of the proof assistant. These may include the following problems, from most to least serious: - False negatives in verifiers lead to undetected violations of the specification, and thus to erroneously classifying buggy software as correct. - False positives in verifiers lead to correct software being incorrectly rejected, hindering the development cycle and confusing the developers. - Crashes (when a verifier or a compiler fails to act on the input program due to an internal error that occurred during the verifier or the compiler execution) are bugs that can lead to inefficient development of software and can confuse the programmer. - Hangs are similar to crashes, but lead to an infinite run of a verifier or a compiler instead of an internal error. In this project, you will focus on testing the software stack of one of the widely-used proof assistants, Isabelle/HOL [6]. Isabelle/HOL has been used to verify an OS Kernel [1], and is used to verify software affecting millions of people in companies like Apple [3] and Amazon [4]. This project will expose you to areas in logic, formal methods, compilers, programming languages, and fuzzing. For your project, you will need to choose a part of the Isabelle/HOL software chain/tool stack and a fuzzing method you wish to try on that part. The likely places to find bugs are in the frontend, interfaces between Isabelle/HOL and other tools, or the compiler that compiles Isabelle/HOL. You will need to choose as part of your variant testing either of them. (Relevant modules: theory/logic modules, compilers, and software engineering ones.) You shall build a new fuzzer (e.g. by writing a new set of code mutations to AFL 1 ) or extend significantly an existing fuzzer and show your extension led to more efficient testing of the target compiler as part of the evaluation of your project. 1 You can use AFL or LibFuzzer to write your own code mutations. Check these links for technical details: AFL Michal Zalewski, ÃÂÃÂÃÂÃÂTechnical ÃÂÃÂÃÂÃÂwhitepaperÃÂÃÂÃÂÃÂ for afl-fuzz,ÃÂÃÂÃÂÃÂ https://lcamtuf.coredump.cx/afl/technical_details.txt ; Google, ÃÂÃÂÃÂÃÂAFL dictionaries,ÃÂÃÂÃÂÃÂ: https://github.com/google/AFL/blob/master/dictionaries/README.dictionaries ; AFL++ https://aflplus.plus ; and LLVM Project, ÃÂÃÂÃÂÃÂlibFuzzer ÃÂÃÂÃÂÃÂ a library for coverage-guided fuzz testing,ÃÂÃÂÃÂÃÂ https://llvm.org/docs/LibFuzzer.html . </br></br><b>Variation 1. </b>
</br></br>The PolyML compiler, which compiles the Isabelle/HOL proof assistant. Here you could find crashes and miscompilation bugs.</br></br><b>Variation 2. </b>
</br></br>The Isabelle Graphical Frontend with the latest stable versions to find crashes or hangs.</br></br><b>Variation 3.</b>
</br></br>The interface between Isabelle and other external provers or tools, which are mostly invoked by sledgehammer.</br></br><b>Variation 4.</b>
</br></br>Testing IsabelleÃÂÃÂÃÂÃÂs unifier, which is a trusted piece of code in IsabelleÃÂÃÂÃÂÃÂs core. Here you might find false negatives/positives.</br></br><b>Variations 5 and 6. </b>
</br></br>Your own variance with other theorem provers, as listed below.</br></br>Please ensure you can run Docker or a virtual machine on your computer before selecting this project. Knowledge of Unix and Ninja/CMake is required for this project. Please open, if you do not already have one, a GitHub account. During the project, you can apply for Amazon EC2 for resources. This is free for 1 year, unless you have already used your free period. Please contact us if this is the case. ( https://aws.amazon.com/free/ ) Deliverables: Mandatory: a final report discussing the architecture of your chosen SUT as part of the background, description of your methodology, your implementation including how your code works on the chosen SUT, how to build form source the SUT, how to instrument it, your methodology to generate new tests, your methodology and results of how to evaluate the effectiveness of testing, and bug reports. Beyond that, you are also expected to submit a presentation , the source code and executable file of the working system and data, as part of the general requirements of individual projects. There will be three different links on KEATS at the end of the project for you to upload: 1. The report 2. Zip/tar of your source code 3. Appendix, which includes a printout of all your code 4. Your presentation, which MUST be under 10 minutes (recommended time is 9 to 9.55 minutes) We strongly encourage you to publish your artefact in Zenodo or figshare. This can include your code and data gathered during your evaluation in a shareable format. We also encourage you to create a dataset and publish it.
</td></tr>
<tr>
    <td>Deliverables:</td>
    <td>Deliverables: Mandatory: a final report discussing the architecture of your chosen SUT as part of the background, description of your methodology, your implementation including how your code works on the chosen SUT, how to build form source the SUT, how to instrument it, your methodology to generate new tests, your methodology and results of how to evaluate the effectiveness of testing, and bug reports. Beyond that, you are also expected to submit a presentation , the source code and executable file of the working system and data, as part of the general requirements of individual projects. There will be three different links on KEATS at the end of the project for you to upload: 1. The report 2. Zip/tar of your source code 3. Appendix, which includes a printout of all your code 4. Your presentation, which MUST be under 10 minutes (recommended time is 9 to 9.55 minutes) We strongly encourage you to publish your artefact in Zenodo or figshare. This can include your code and data gathered during your evaluation in a shareable format. We also encourage you to create a dataset and publish it.</td>
</tr>
<tr>
    <td>Description URL:</td>
    <td>
        <a class="under" href=""></a>
    </td>
</tr>
<tr>
    <td>Programmes:</td>
    <td>
        BSc Computer Science (Full Time)<br/>
        BSc Computer Science with Management (Full Time)<br/>
    </td>
</tr>
<tr>
    <td>Non-standard hardware/software required:</td>
    <td>No</td>
</tr>
<tr>
    <td>Project status:</td>
    <td>
        <b>Allocated</b>
    </td>
</tr>
<tr>
    <td>Student name:</td>
    <td>Lin, Qilan</td>
</tr>
</table>
