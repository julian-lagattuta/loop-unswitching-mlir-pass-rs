use std::{env, error::Error, fs, io};
use melior::{
    Context, dialect::DialectRegistry, ir::{Module, operation::OperationLike}, utility::register_all_dialects,
};

mod loop_unswitching;
fn main() -> Result<(), Box<dyn Error>> {
    let path = env::args_os().nth(1).ok_or_else(|| {
        io::Error::new(
            io::ErrorKind::InvalidInput,
            "usage: scftowavelet <input.mlir>",
        )
    })?;
    let source = fs::read_to_string(&path)?;

    let registry = DialectRegistry::new();
    register_all_dialects(&registry);

    let context = Context::new_with_registry(&registry, false);
    for dialect in ["memref", "arith", "func", "scf"] {
        context.get_or_load_dialect(dialect);
    }

    let mut module = Module::parse(&context, &source).ok_or_else(|| {
        io::Error::new(
            io::ErrorKind::InvalidData,
            format!("failed to parse MLIR file: {}", path.to_string_lossy()),
        )
    })?;

    loop_unswitching::loop_unswitch(&context, &mut module);
    
    fs::write("out.mlir", module.as_operation().to_string()).unwrap();
    if !module.as_operation().verify(){
        println!("failed to verify");
    }
    // println!("{}",op);
    Ok(())
}
