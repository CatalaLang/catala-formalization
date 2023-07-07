
snippets/ltac2_tuto/: ../theories/common/ltac2_tuto.v
	$(alectryon) "$<"
	@touch "$@"


snippets/MyTactics/: ../theories/common/MyTactics.v
	$(alectryon) "$<"
	@touch "$@"


snippets/FixExtra/: ../theories/common/FixExtra.v
	$(alectryon) "$<"
	@touch "$@"


snippets/Diagrams/: ../theories/common/Diagrams.v
	$(alectryon) "$<"
	@touch "$@"


snippets/MySequences/: ../theories/common/MySequences.v
	$(alectryon) "$<"
	@touch "$@"


snippets/scratch/: ../theories/common/scratch.v
	$(alectryon) "$<"
	@touch "$@"


snippets/Simulation/: ../theories/common/Simulation.v
	$(alectryon) "$<"
	@touch "$@"


snippets/scratch2/: ../theories/common/scratch2.v
	$(alectryon) "$<"
	@touch "$@"


snippets/MyRelations/: ../theories/common/MyRelations.v
	$(alectryon) "$<"
	@touch "$@"


snippets/LibTactics/: ../theories/common/LibTactics.v
	$(alectryon) "$<"
	@touch "$@"


snippets/Option/: ../theories/common/Option.v
	$(alectryon) "$<"
	@touch "$@"


snippets/Procrastination/: ../theories/common/Procrastination.v
	$(alectryon) "$<"
	@touch "$@"


snippets/MyList/: ../theories/common/MyList.v
	$(alectryon) "$<"
	@touch "$@"


snippets/AutosubstExtra/: ../theories/autosubst_extra/AutosubstExtra.v
	$(alectryon) "$<"
	@touch "$@"


snippets/Autosubst_IsRen/: ../theories/autosubst_extra/Autosubst_IsRen.v
	$(alectryon) "$<"
	@touch "$@"


snippets/Autosubst_FreeVars/: ../theories/autosubst_extra/Autosubst_FreeVars.v
	$(alectryon) "$<"
	@touch "$@"


snippets/Autosubst_EOS/: ../theories/autosubst_extra/Autosubst_EOS.v
	$(alectryon) "$<"
	@touch "$@"


snippets/Autosubst_Env/: ../theories/autosubst_extra/Autosubst_Env.v
	$(alectryon) "$<"
	@touch "$@"


snippets/STLCTypeSoundness/: ../theories/lcalc/STLCTypeSoundness.v
	$(alectryon) "$<"
	@touch "$@"


snippets/LCFreeVars/: ../theories/lcalc/LCFreeVars.v
	$(alectryon) "$<"
	@touch "$@"


snippets/LCSyntax/: ../theories/lcalc/LCSyntax.v
	$(alectryon) "$<"
	@touch "$@"


snippets/STLCDefinition/: ../theories/lcalc/STLCDefinition.v
	$(alectryon) "$<"
	@touch "$@"


snippets/continuation/: ../theories/lcalc/continuation.v
	$(alectryon) "$<"
	@touch "$@"


snippets/LCReduction/: ../theories/lcalc/LCReduction.v
	$(alectryon) "$<"
	@touch "$@"


snippets/LCValues/: ../theories/lcalc/LCValues.v
	$(alectryon) "$<"
	@touch "$@"


snippets/DCtoLC/: ../theories/mcalc/DCtoLC.v
	$(alectryon) "$<"
	@touch "$@"


snippets/DCValues/: ../theories/dcalc/DCValues.v
	$(alectryon) "$<"
	@touch "$@"


snippets/STDCLemmas/: ../theories/dcalc/STDCLemmas.v
	$(alectryon) "$<"
	@touch "$@"


snippets/DCErrors/: ../theories/dcalc/DCErrors.v
	$(alectryon) "$<"
	@touch "$@"


snippets/DCValuesRes/: ../theories/dcalc/DCValuesRes.v
	$(alectryon) "$<"
	@touch "$@"


snippets/DCReduction/: ../theories/dcalc/DCReduction.v
	$(alectryon) "$<"
	@touch "$@"


snippets/DCBigStep/: ../theories/dcalc/DCBigStep.v
	$(alectryon) "$<"
	@touch "$@"


snippets/DCFreeVars/: ../theories/dcalc/DCFreeVars.v
	$(alectryon) "$<"
	@touch "$@"


snippets/DCSyntax/: ../theories/dcalc/DCSyntax.v
	$(alectryon) "$<"
	@touch "$@"


snippets/STDCDefinition/: ../theories/dcalc/STDCDefinition.v
	$(alectryon) "$<"
	@touch "$@"


snippets/STDCTypeSoundness/: ../theories/dcalc/STDCTypeSoundness.v
	$(alectryon) "$<"
	@touch "$@"

targets := snippets/ltac2_tuto/ snippets/MyTactics/ snippets/FixExtra/ snippets/Diagrams/ snippets/MySequences/ snippets/scratch/ snippets/Simulation/ snippets/scratch2/ snippets/MyRelations/ snippets/LibTactics/ snippets/Option/ snippets/Procrastination/ snippets/MyList/ snippets/AutosubstExtra/ snippets/Autosubst_IsRen/ snippets/Autosubst_FreeVars/ snippets/Autosubst_EOS/ snippets/Autosubst_Env/ snippets/STLCTypeSoundness/ snippets/LCFreeVars/ snippets/LCSyntax/ snippets/STLCDefinition/ snippets/continuation/ snippets/LCReduction/ snippets/LCValues/ snippets/DCtoLC/ snippets/DCValues/ snippets/STDCLemmas/ snippets/DCErrors/ snippets/DCValuesRes/ snippets/DCReduction/ snippets/DCBigStep/ snippets/DCFreeVars/ snippets/DCSyntax/ snippets/STDCDefinition/ snippets/STDCTypeSoundness/
