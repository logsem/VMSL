# Meeting Notes

## Sept. 4
- Long term goal: to specify and verify properties of a real hypervisor, formalize in Coq
- Sub problem areas towards the long term goal:
	- What is a hypervisor?
		- actual code, intuitive understanding, model implementations
		- [Alix gives first presentation]
	- State-of-the-art for hypervisor-like specification and verification
              - E. Cohen hypervisor verification 
              	- <https://link.springer.com/chapter/10.1007%2F11813040_6>
              	- <https://link.springer.com/chapter/10.1007%2F978-3-642-35843-2_1>
              - Sel4, Prove-and-run, Certikos
	- Toolbox-verification techniques
		- Iris experiments with NI:
			- SeLoC for TSNI <https://iris-project.org/pdfs/2020-seloc-submission.pdf>
			- TINI <projects/logsem/iris-logrel/noninterference/POPL21/paper.pdf>
		- Iris for C
			- RefinedC <https://plv.mpi-sws.org/refinedc/paper.pdf>
	- Literature on variations on NI
		- see list from Dan Frumin<https://bitbucket.org/logsem/hypervisor-verification/src/master/literature.md>
		- also need papers on declassification, delimited release, ... (weaker notions of NI)