// The ROCCC Compiler Infrastructure
//  This file is distributed under the University of California Open Source
//  License.  See ROCCCLICENSE.TXT for details.

#include "common/system_specific.h"
#include "suifkernel/suif_env.h"
#include "suifkernel/module_subsystem.h"

// Pass headers
#include "raw_elimination_pass.h"
#include "scalar_replacement_pass.h"
#include "scalar_replacement_pass2.h"
#include "renaming_pass.h"
#include "feedback_load_elimination_pass.h"
#include "systolic_array_generation_pass.h"
#include "constant_array_propagation_pass.h"
#include "lut_detection_pass.h"
#include "lut_transformation_pass.h"

// External initializations
extern "C" void init_suifnodes(SuifEnv *);
extern "C" void init_cfenodes(SuifEnv *);

extern "C" void init_array_transforms(SuifEnv *suif_env) {
    // Ensure required modules are loaded
    suif_env->require_module("suifnodes");
    suif_env->require_module("cfenodes");
    suif_env->require_module("utils");

    // Register transformation passes
    ModuleSubSystem *module_subsystem = suif_env->get_module_subsystem();

    module_subsystem->register_module(new RawEliminationPass(suif_env));
    module_subsystem->register_module(new ScalarReplacementPass(suif_env));
    module_subsystem->register_module(new ScalarReplacementPass2(suif_env));
    module_subsystem->register_module(new RenamingPass(suif_env));
    module_subsystem->register_module(new FeedbackLoadEliminationPass(suif_env));
    module_subsystem->register_module(new SystolicArrayGenerationPass(suif_env));
    module_subsystem->register_module(new ConstantArrayPropagationPass(suif_env));
    module_subsystem->register_module(new LUTDetectionPass(suif_env));
    module_subsystem->register_module(new LUTTransformationPass(suif_env));
}
