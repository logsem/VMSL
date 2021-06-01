# Hypervisors for dummies

Hypervisors or virtual machines manager (VMM) are software used to allow one
host machine to support multiple guest VMs. This is especially useful for cloud
environments where virtual machines need to be quickly provisioned. Another
possible usage is as a secure partition manager, providing isolation between
different set of security domains.

There are two types of hypervisors, referred to as "Type 1" and "Type 2". The
former corresponds to hypervisors that run directly on the bare metal, while the
latter run as software over an operating system. Type 1 hypervisors are
obviously more efficient and will be the focus of the rest of these notes.

An hypervisor acts as a virtualization layer for the guest VMs, it ensures that
VMs run "as if" on bare metal (with a few caveats). VMs thus have associated
vCPUs, memory, etc. The hypervisor needs to ensure that those resources are
isolated between the VMs.

For that purpose, we focus on how this is achieved by
[Hafnium](https://hafnium.googlesource.com/hafnium/). Its architecture is
described more precisely
[here](https://hafnium.googlesource.com/hafnium/+/HEAD/docs/Architecture.md).

Current architectures support different privilege levels usually numbered from 0
to 3, where level 0 corresponds to having the most privilege. Though, on ARM
architecture, these are called "Exception levels" and numbering is inversed,
i.e., EL3 corresponds to having the most privilege rather than EL0. Usually, the
common usage model is that a secure firmware runs on EL3, EL2 is used by an
hypervisor, an OS runs on EL1, and EL0 is used by application code (see
[here](https://developer.arm.com/architectures/learn-the-architecture/exception-model/privilege-and-exception-levels)
for more details).

Another feature of current architectures is a virtual memory system managed by a
memory management unit (MMU). The MMU can be programmed by software running at
sufficient privilege level. The MMU maintains the page tables used to translate
the virtual addresses used by the software to the corresponding physical
addresses. In particular, an hypervisor running at EL2 can control in this way
the memory resources that can be accessed by different VMs (see
[here](https://developer.arm.com/architectures/learn-the-architecture/armv8-a-virtualization/stage-2-translation)
for more details). Therefore, checking memory isolation can be reduced to
verifying that page tables are correctly set up by the hypervisor.

As an hypervisor can host any number of VMs, it is necessary to have a scheduler
choosing which VM runs at which point. Usually, this is part of the job of the
hypervisor to schedule the different VMs. However, Hafnium relies instead on a
primary VM (e.g., Android or Linux) to handle scheduling. The rationale is (1)
to avoid complexity in Hafnium, (2) no availability guarantee is provided so it
is fine for the (potentially compromised) primary VM to deny secondary VMs, and
(3) a lot of effort has already been put in the Android/Linux scheduler, it
would be redundant to re-implement. When switching from running one VM to
another, the hypervisor must ensure that the state (registers, etc) is saved.

Another point is that memory is not truly isolated between VMs: they can decide
to share, lend, or donate memory to another VM. This complicates the security
condition: memory that are not shared cannot be read by other VMs, nor tampered
(confidentiality & integrity).

## [Hafnium's attacker model](https://hafnium.googlesource.com/hafnium/+/HEAD/docs/Architecture.md#security-model)

Hafnium runs a set of VMs without trusting any of them. Hafnium aims to
guarantee memory confidentiality and integrity of each VM: no other VM can read
nor modify the memory to a VM without that VM's consent. This implies that
Hafnium cannot be hijacked by a VM.

