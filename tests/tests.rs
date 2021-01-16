use std::process::Command;

fn run_test(test_name: &str) {
  let cargo_sync_readme_dir = std::env::current_dir().unwrap();

  let cargo_sync_readme_bin = {
    let name = std::env::var("CARGO_PKG_NAME").unwrap();

    // This ensures the tests run in windows as well.
    [&name, &format!("{}.exe", name)]
      .iter()
      .map(|filename| {
        cargo_sync_readme_dir
          .join("target")
          .join("debug")
          .join(filename)
      })
      .find(|bin| bin.is_file())
      .expect(&format!("{} binary not found", name))
  };

  let test_dir = cargo_sync_readme_dir.join("tests").join(test_name);

  if !test_dir.is_dir() {
    panic!("Test directory not found: {}", test_dir.display());
  }

  let expected_readme = test_dir.join("README-expected.md");

  if !expected_readme.is_file() {
    panic!("Expected readme not found: {}", expected_readme.display());
  }

  let template_readme = test_dir.join("README-template.md");

  if !template_readme.is_file() {
    panic!("Template readme not found: {}", template_readme.display());
  }

  let readme = test_dir.join("README.md");

  std::fs::copy(&template_readme, &readme).unwrap();

  let output = Command::new(&cargo_sync_readme_bin)
    .arg("sync-readme")
    .current_dir(test_dir)
    .output()
    .expect(&format!(
      "Failed to execute {}",
      cargo_sync_readme_bin.display()
    ));

  let expected = std::fs::read_to_string(&expected_readme).unwrap();
  let got = std::fs::read_to_string(&readme).unwrap();

  // To ensure this works on windows, we ignore '\r'.
  let got = got.replace("\r", "");

  if expected != got {
    let in_ci = std::env::var_os("CI").is_some();

    let diff_msg = match in_ci {
      true => format!("==== Expected ====\n{}\n==== Got ====\n{}", expected, got),
      false => format!(
        "See the diff with `diff {} {}`.",
        readme.display(),
        expected_readme.display()
      ),
    };

    let stderr = String::from_utf8_lossy(&output.stderr);

    panic!(
      "The generated README does not match what was expected.\n\n{}\n==== stderr ====\n{}",
      diff_msg, stderr
    );
  }
}

#[test]
fn integration_test_intralinks_simple() {
  run_test("intralinks_simple");
}

#[test]
fn integration_test_intralinks_module_walk() {
  run_test("intralinks_module_walk");
}

#[test]
fn integration_test_intralinks_ambiguous_module() {
  run_test("intralinks_ambiguous_module");
}

#[test]
fn integration_test_intralinks_stdlib_links() {
  run_test("intralinks_stdlib_links");
}
