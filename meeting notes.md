# Meeting Notes

## Sept. 4
-------
- Long term goal: to specify and verify properties of a real hypervisor, formalize in Coq
- Sub problem areas towards the long term goal:
	- What is a hypervisor?
		- actual code, intuitive understanding, model implementations
		- [Alix gives first presentation]
	- State-of-the-art for hypervisor-like specification and verification
		- E. Cohen hypervisor verification 
			- <https://link.springer.com/chapter/10.1007%2F11813040_6> 
			- <https://link.springer.com/chapter/10.1007%2F978-3-642-35843-2_1> 
		- sel4, Prove-and-run, Certikos
	- Toolbox-verification techniques
		- Iris experiments with NI:
			- SeLoC for TSNI <https://iris-project.org/pdfs/2020-seloc-submission.pdf>
			- TINI <projects/logsem/iris-logrel/noninterference/POPL21/paper.pdf>
		- Iris for C
			- RefinedC <https://plv.mpi-sws.org/refinedc/paper.pdf>
	- Literature on variations on NI
		- see list from Dan Frumin<https://bitbucket.org/logsem/hypervisor-verification/src/master/literature.md>
		- also need papers on declassification, delimited release, ... (weaker notions of NI)
		
## Jan. 8
-------
- comments the call/cc approach
  - only verify a simplified implementation at beginning
	- no formally connections with the real implementation
  - writing the implementation in assembly language is tricky, prefer using a C-like language for the implementation
	- then preferably the specification side(client programs running in VMs) should be also written in a C-like language
	- a pure C-like language is insufficient
		- require inline assmebly to manipulate hardware like system registers etc.(for both VMs and the hypervisor)
	- how to handle the mix of C-like and inline assembly?
		- how to define semantics?
		- Alix: <https://sf.snu.ac.kr/compcertm/>
- short term plans
  - goal: verify client programs
  - develop program logic for the operational semantics we have been working on
	- read the iris ground up paper again to see how the weakest precondition was defined for Heaplang
  - try to verify small interesting examples
  - read more hypervisor papers
  - next friday: discuss two papers by Ernie Cohen
  - friday after next: skip(attend POPL)
