use stl_compiler::{parser::STLParser, Compiler, CompilerConfig};

#[tokio::test]
async fn parses_grid_spec_line() {
    let compiler = Compiler::new(CompilerConfig::for_tests_without_external_tools());
    let result = compiler
        .compile("grid_spec\nvoltage > 220")
        .await
        .expect("compile");
    assert!(result.smt_output.smt_lib_code.contains("(set-logic"));
}

#[test]
fn parser_rejects_empty_input() {
    let mut parser = STLParser::new();
    assert!(parser.parse("").is_err());
}
