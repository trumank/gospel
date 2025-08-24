import minimal_module::additional_module_file::MinimalStruct;

input int GLOBAL_WITH_DEFAULT = 3;

struct DependentStruct {
    MinimalStruct field;
    if (GLOBAL_WITH_DEFAULT == 3) {
        short int hello;
    } else {
        long long int hello;
        void* test;
    };
    (if (GLOBAL_WITH_DEFAULT == 2) int else long int) cond_type;
};
