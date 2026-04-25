// Licensed to Julian Hyde under one or more contributor license
// agreements.  See the NOTICE file distributed with this work
// for additional information regarding copyright ownership.
// Julian Hyde licenses this file to you under the Apache
// License, Version 2.0 (the "License"); you may not use this
// file except in compliance with the License.  You may obtain a
// copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing,
// software distributed under the License is distributed on an
// "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND,
// either express or implied.  See the License for the specific
// language governing permissions and limitations under the
// License.

extern crate core;
use crate::shell::{ScriptTest, Shell as ShellMain};
use std::env;
use std::io::{IsTerminal, Read, Write, stdin, stdout};
use std::process::exit;

mod compile;
mod eval;
mod shell;
mod syntax;
mod unify;

/// Result of parsing command-line arguments. `main()` dispatches on this;
/// unit tests assert on it directly.
#[derive(Eq, PartialEq, Debug)]
enum CliAction {
    Help,
    Command(String),
    Test(Vec<String>),
    Interactive {
        directory: Option<String>,
    },
    Scripts {
        /// Non-empty; "-" means stdin.
        files: Vec<String>,
        force_idempotent: Option<bool>,
        directory: Option<String>,
    },
    /// An argument parse error; the string is shown on stderr before exit 1.
    Error(String),
}

/// Parses command-line arguments (excluding `argv\[0\]`) into a `CliAction`.
fn parse_args(args: &[String]) -> CliAction {
    // Special subcommands take precedence and consume the rest of argv.
    if let Some(first) = args.first() {
        match first.as_str() {
            "-h" | "--help" => return CliAction::Help,
            "test" => return CliAction::Test(args[1..].to_vec()),
            "-c" => {
                return match args.get(1) {
                    Some(cmd) => CliAction::Command(cmd.clone()),
                    None => CliAction::Error(
                        "-c requires a command argument".into(),
                    ),
                };
            }
            _ => {}
        }
    }

    // Parse flags and files. Flags may be interleaved with files; a bare
    // '--' ends flag parsing.
    let mut force_idempotent: Option<bool> = None;
    let mut directory: Option<String> = None;
    let mut files: Vec<String> = Vec::new();
    let mut end_of_flags = false;
    for arg in args {
        if end_of_flags {
            files.push(arg.clone());
            continue;
        }
        match arg.as_str() {
            "--" => end_of_flags = true,
            "--idempotent" => force_idempotent = Some(true),
            "--no-idempotent" => force_idempotent = Some(false),
            _ if arg.starts_with("--directory=") => {
                directory =
                    Some(arg.strip_prefix("--directory=").unwrap().to_string());
            }
            _ if arg.starts_with("--") => {
                return CliAction::Error(format!("Unknown option: {}", arg));
            }
            _ => files.push(arg.clone()),
        }
    }

    if files.is_empty() && force_idempotent.is_none() {
        CliAction::Interactive { directory }
    } else {
        if files.is_empty() {
            files.push("-".to_string());
        }
        CliAction::Scripts {
            files,
            force_idempotent,
            directory,
        }
    }
}

/// Runs a non-empty list of script files (where "-" means stdin) through the
/// given shell, setting `config.idempotent` per file: `force_idempotent`
/// wins if `Some`, otherwise the `.smli` suffix determines idempotent mode.
/// Output from every file is written to `output`.
fn run_scripts_with<R: Read, W: Write>(
    shell: &mut ShellMain,
    files: &[String],
    force_idempotent: Option<bool>,
    stdin_reader: R,
    mut output: W,
) -> Result<(), (String, String)> {
    // Script mode: no banner, no prompts, echo input lines (transcript).
    shell.config.banner = Some(false);
    shell.config.prompt = Some(false);
    shell.config.stdin_is_tty = Some(false);
    shell.config.echo = Some(true);

    // Ensure stdin can only be consumed by one "-" entry.
    let mut stdin_once = Some(stdin_reader);
    for file in files {
        let idempotent = match force_idempotent {
            Some(force) => force,
            None => file.ends_with(".smli"),
        };
        shell.config.idempotent = Some(idempotent);

        let result = if file == "-" {
            match stdin_once.take() {
                Some(s) => shell.run(s, &mut output),
                None => {
                    return Err((
                        file.clone(),
                        "standard input already consumed by an earlier '-' \
                         argument"
                            .into(),
                    ));
                }
            }
        } else {
            shell.run_file(file, &mut output)
        };
        if let Err(e) = result {
            return Err((file.clone(), e.to_string()));
        }
    }
    Ok(())
}

fn print_help() {
    println!("morel-rust version {}", env!("CARGO_PKG_VERSION"));
    println!();
    println!("Usage: morel [OPTIONS] [FILES...]");
    println!("       morel -c COMMAND");
    println!("       morel test [FILES...]");
    println!("       morel -h | --help");
    println!();
    println!("Options:");
    println!("  -h, --help         Print this help message and exit");
    println!("  -c COMMAND         Execute a single command and exit");
    println!(
        "  --idempotent       Force idempotent mode for all files and stdin"
    );
    println!(
        "  --no-idempotent    Force non-idempotent mode for all files / stdin"
    );
    println!("  --directory=DIR    Set the working directory");
    println!(
        "  --                 End of options; remaining args are file names"
    );
    println!();
    println!("Arguments:");
    println!(
        "  FILES...           Morel script files to run. Use '-' for stdin."
    );
    println!("                     With no files (and no --idempotent/");
    println!(
        "                     --no-idempotent), an interactive REPL reads"
    );
    println!("                     from standard input.");
    println!();
    println!("Modes:");
    println!(
        "  By default, each file runs in idempotent mode if its suffix is"
    );
    println!(
        "  '.smli', otherwise in normal (transcript) mode. --idempotent /"
    );
    println!("  --no-idempotent override the per-file default.");
    println!();
    println!("  Idempotent mode: echoes input and prefixes results with '> '.");
    println!(
        "  Output reproduces the .smli test-file format (round-trip-safe)."
    );
    println!();
    println!(
        "  Normal mode: echoes input only (no '> ' prefix); a transcript."
    );
    println!();
    println!("Examples:");
    println!("  morel                         Interactive REPL");
    println!("  morel -c \"1 + 2\"              Execute a single command");
    println!("  morel script.sml              Run script, transcript mode");
    println!("  morel script.smli             Run script, idempotent mode");
    println!(
        "  morel a.sml b.smli            Run two scripts (mode per suffix)"
    );
    println!("  morel --idempotent < file     Run stdin in idempotent mode");
    println!("  morel --no-idempotent x.smli  Override suffix rule");
    println!("  morel test [files...]         Run script tests");
}

fn main() {
    let args: Vec<String> = env::args().collect();
    match parse_args(&args[1..]) {
        CliAction::Help => {
            print_help();
            exit(0);
        }
        CliAction::Error(msg) => {
            eprintln!("{}", msg);
            exit(1);
        }
        CliAction::Test(test_args) => match ScriptTest::main(&test_args) {
            Ok(()) => {
                println!("All tests completed successfully");
                exit(0);
            }
            Err(e) => {
                eprintln!("Test error: {}", e);
                exit(1);
            }
        },
        CliAction::Command(cmd) => {
            let mut shell = ShellMain::new(&[]);
            match shell.run_command(&cmd, stdout()) {
                Ok(()) => exit(0),
                Err(e) => {
                    eprintln!("Error executing command: {}", e);
                    exit(1);
                }
            }
        }
        CliAction::Interactive { directory } => {
            run_interactive(directory.as_deref());
        }
        CliAction::Scripts {
            files,
            force_idempotent,
            directory,
        } => {
            let mut shell_args: Vec<String> = Vec::new();
            if let Some(dir) = &directory {
                shell_args.push(format!("--directory={}", dir));
            }
            let mut shell = ShellMain::new(&shell_args);
            match run_scripts_with(
                &mut shell,
                &files,
                force_idempotent,
                stdin(),
                stdout(),
            ) {
                Ok(()) => exit(0),
                Err((file, msg)) => {
                    eprintln!("Error running {}: {}", file, msg);
                    exit(1);
                }
            }
        }
    }
}

fn run_interactive(directory: Option<&str>) {
    let mut shell_args = vec!["--prompt".to_string(), "--banner".to_string()];
    if IsTerminal::is_terminal(&stdin()) {
        shell_args.push("--tty".to_string());
    }
    if let Some(dir) = directory {
        shell_args.push(format!("--directory={}", dir));
    }
    let mut main = ShellMain::new(&shell_args);
    match main.run(stdin(), stdout()) {
        Ok(()) => {
            println!("Goodbye!");
        }
        Err(e) => {
            eprintln!("Shell error: {}", e);
            exit(1);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;
    use std::io::{Cursor, empty};
    use std::path::PathBuf;
    use std::process::id;

    fn s(x: &str) -> String {
        x.to_string()
    }

    // parse_args tests

    #[test]
    fn test_parse_args_empty_is_interactive() {
        assert_eq!(parse_args(&[]), CliAction::Interactive { directory: None });
    }

    #[test]
    fn test_parse_args_help() {
        assert_eq!(parse_args(&[s("-h")]), CliAction::Help);
        assert_eq!(parse_args(&[s("--help")]), CliAction::Help);
    }

    #[test]
    fn test_parse_args_dash_c_with_command() {
        assert_eq!(
            parse_args(&[s("-c"), s("1 + 2")]),
            CliAction::Command("1 + 2".into())
        );
    }

    #[test]
    fn test_parse_args_dash_c_without_command_is_error() {
        match parse_args(&[s("-c")]) {
            CliAction::Error(msg) => assert!(msg.contains("-c")),
            other => panic!("expected Error, got {:?}", other),
        }
    }

    #[test]
    fn test_parse_args_test_subcommand() {
        assert_eq!(
            parse_args(&[s("test"), s("a.smli"), s("b.smli")]),
            CliAction::Test(vec![s("a.smli"), s("b.smli")])
        );
    }

    #[test]
    fn test_parse_args_single_file() {
        assert_eq!(
            parse_args(&[s("foo.smli")]),
            CliAction::Scripts {
                files: vec![s("foo.smli")],
                force_idempotent: None,
                directory: None,
            }
        );
    }

    #[test]
    fn test_parse_args_multiple_files() {
        assert_eq!(
            parse_args(&[s("a.sml"), s("b.smli")]),
            CliAction::Scripts {
                files: vec![s("a.sml"), s("b.smli")],
                force_idempotent: None,
                directory: None,
            }
        );
    }

    #[test]
    fn test_parse_args_idempotent_with_no_file_implies_stdin() {
        assert_eq!(
            parse_args(&[s("--idempotent")]),
            CliAction::Scripts {
                files: vec![s("-")],
                force_idempotent: Some(true),
                directory: None,
            }
        );
    }

    #[test]
    fn test_parse_args_no_idempotent_overrides_suffix() {
        assert_eq!(
            parse_args(&[s("--no-idempotent"), s("x.smli")]),
            CliAction::Scripts {
                files: vec![s("x.smli")],
                force_idempotent: Some(false),
                directory: None,
            }
        );
    }

    #[test]
    fn test_parse_args_directory_flag() {
        assert_eq!(
            parse_args(&[s("--directory=/tmp"), s("f.sml")]),
            CliAction::Scripts {
                files: vec![s("f.sml")],
                force_idempotent: None,
                directory: Some("/tmp".into()),
            }
        );
    }

    #[test]
    fn test_parse_args_double_dash_ends_flags() {
        // Without --, a file name starting with -- would error as an
        // unknown flag; with --, it's taken as a file name.
        assert_eq!(
            parse_args(&[s("--"), s("--looks-like-flag")]),
            CliAction::Scripts {
                files: vec![s("--looks-like-flag")],
                force_idempotent: None,
                directory: None,
            }
        );
    }

    #[test]
    fn test_parse_args_unknown_flag_is_error() {
        match parse_args(&[s("--whatever")]) {
            CliAction::Error(msg) => assert!(
                msg.contains("--whatever"),
                "error message should mention the flag: {}",
                msg
            ),
            other => panic!("expected Error, got {:?}", other),
        }
    }

    #[test]
    fn test_parse_args_flags_may_follow_files() {
        // Before '--' is hit, flags parse wherever they appear.
        assert_eq!(
            parse_args(&[s("a.sml"), s("--idempotent"), s("b.sml")]),
            CliAction::Scripts {
                files: vec![s("a.sml"), s("b.sml")],
                force_idempotent: Some(true),
                directory: None,
            }
        );
    }

    #[test]
    fn test_parse_args_dash_is_stdin_literal() {
        assert_eq!(
            parse_args(&[s("-")]),
            CliAction::Scripts {
                files: vec![s("-")],
                force_idempotent: None,
                directory: None,
            }
        );
    }

    // run_scripts_with tests — these actually execute morel code.

    /// Builds a uniquely-named temp file path for a test.
    fn temp_path(test_name: &str, ext: &str) -> PathBuf {
        let pid = id();
        env::temp_dir()
            .join(format!("morel_main_{}_{}.{}", test_name, pid, ext))
    }

    #[test]
    fn test_run_scripts_smli_suffix_enables_idempotent() {
        let path = temp_path("smli_suffix", "smli");
        fs::write(&path, "val x = 1;\n").unwrap();

        let mut shell = ShellMain::new(&[]);
        let mut output = Vec::new();
        run_scripts_with(
            &mut shell,
            &[path.to_string_lossy().to_string()],
            None,
            empty(),
            &mut output,
        )
        .unwrap();

        assert_eq!(
            String::from_utf8(output).unwrap(),
            "val x = 1;\n> val x = 1 : int\n"
        );
        let _ = fs::remove_file(&path);
    }

    #[test]
    fn test_run_scripts_sml_suffix_is_transcript() {
        let path = temp_path("sml_suffix", "sml");
        fs::write(&path, "val x = 1;\n").unwrap();

        let mut shell = ShellMain::new(&[]);
        let mut output = Vec::new();
        run_scripts_with(
            &mut shell,
            &[path.to_string_lossy().to_string()],
            None,
            empty(),
            &mut output,
        )
        .unwrap();

        // Transcript: input echoed, no "> " prefix.
        assert_eq!(
            String::from_utf8(output).unwrap(),
            "val x = 1;\nval x = 1 : int\n"
        );
        let _ = fs::remove_file(&path);
    }

    #[test]
    fn test_run_scripts_force_idempotent_overrides_sml_suffix() {
        let path = temp_path("force_idempotent", "sml");
        fs::write(&path, "val x = 1;\n").unwrap();

        let mut shell = ShellMain::new(&[]);
        let mut output = Vec::new();
        run_scripts_with(
            &mut shell,
            &[path.to_string_lossy().to_string()],
            Some(true),
            empty(),
            &mut output,
        )
        .unwrap();

        assert_eq!(
            String::from_utf8(output).unwrap(),
            "val x = 1;\n> val x = 1 : int\n"
        );
        let _ = fs::remove_file(&path);
    }

    #[test]
    fn test_run_scripts_force_no_idempotent_overrides_smli_suffix() {
        let path = temp_path("force_no_idempotent", "smli");
        fs::write(&path, "val x = 1;\n").unwrap();

        let mut shell = ShellMain::new(&[]);
        let mut output = Vec::new();
        run_scripts_with(
            &mut shell,
            &[path.to_string_lossy().to_string()],
            Some(false),
            empty(),
            &mut output,
        )
        .unwrap();

        assert_eq!(
            String::from_utf8(output).unwrap(),
            "val x = 1;\nval x = 1 : int\n"
        );
        let _ = fs::remove_file(&path);
    }

    #[test]
    fn test_run_scripts_state_persists_across_files() {
        let p1 = temp_path("state_1", "sml");
        let p2 = temp_path("state_2", "sml");
        fs::write(&p1, "val x = 10;\n").unwrap();
        fs::write(&p2, "x + 1;\n").unwrap();

        let mut shell = ShellMain::new(&[]);
        let mut output = Vec::new();
        run_scripts_with(
            &mut shell,
            &[
                p1.to_string_lossy().to_string(),
                p2.to_string_lossy().to_string(),
            ],
            None,
            empty(),
            &mut output,
        )
        .unwrap();

        let out = String::from_utf8(output).unwrap();
        assert!(
            out.contains("val x = 10 : int"),
            "expected x = 10 result; got: {}",
            out
        );
        // Second file uses x from the first.
        assert!(
            out.contains("val it = 11 : int"),
            "expected 'val it = 11 : int' from x+1; got: {}",
            out
        );
        let _ = fs::remove_file(&p1);
        let _ = fs::remove_file(&p2);
    }

    #[test]
    fn test_run_scripts_mixed_suffixes_use_per_file_mode() {
        let p_sml = temp_path("mixed", "sml");
        let p_smli = temp_path("mixed", "smli");
        fs::write(&p_sml, "val a = 1;\n").unwrap();
        fs::write(&p_smli, "val b = 2;\n").unwrap();

        let mut shell = ShellMain::new(&[]);
        let mut output = Vec::new();
        run_scripts_with(
            &mut shell,
            &[
                p_sml.to_string_lossy().to_string(),
                p_smli.to_string_lossy().to_string(),
            ],
            None,
            empty(),
            &mut output,
        )
        .unwrap();

        let out = String::from_utf8(output).unwrap();
        // .sml output has no "> " prefix; .smli does.
        assert!(
            out.contains("\nval a = 1 : int\n"),
            "expected transcript-style 'val a = 1 : int' (no '>'); got: {}",
            out
        );
        assert!(
            out.contains("\n> val b = 2 : int\n"),
            "expected idempotent-style '> val b = 2 : int'; got: {}",
            out
        );
        let _ = fs::remove_file(&p_sml);
        let _ = fs::remove_file(&p_smli);
    }

    #[test]
    fn test_run_scripts_stdin_reads_from_reader() {
        let mut shell = ShellMain::new(&[]);
        let mut output = Vec::new();
        run_scripts_with(
            &mut shell,
            &[s("-")],
            Some(true),
            Cursor::new(b"val x = 1;\n".to_vec()),
            &mut output,
        )
        .unwrap();

        assert_eq!(
            String::from_utf8(output).unwrap(),
            "val x = 1;\n> val x = 1 : int\n"
        );
    }
}
