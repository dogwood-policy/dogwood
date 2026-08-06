//! The `dogwood` command-line tool.
//!
//! A local checker/replayer for Dogwood policies: parse, validate, lower to
//! Cedar, and replay an event trace. It is a thin shell over the
//! `dogwood-language` frontend — the [`ops`] module drives the frontend and
//! returns owned, serializable reports, and this file plus [`render`] handle
//! argument parsing, file I/O, and output formatting.

use std::path::PathBuf;
use std::process::ExitCode;

use clap::{Args, Parser, Subcommand, ValueEnum};

mod error;
mod ops;
mod render;

use error::OpError;
use ops::SchemaInputs;

/// Local checker and replayer for Dogwood policies.
#[derive(Parser)]
#[command(name = "dogwood", version, about, long_about = None)]
struct Cli {
    #[command(subcommand)]
    command: Command,
}

/// Output format shared by every command.
#[derive(Copy, Clone, PartialEq, Eq, ValueEnum, Default)]
enum Format {
    /// Human-readable text, with miette-rendered source snippets for errors.
    #[default]
    Human,
    /// Machine-readable JSON.
    Json,
}

/// The service-schema override flags, shared by the pipeline commands. All
/// optional; omit for the default event schema (request/response/error), no
/// providers, and the default macros.
#[derive(Args, Default)]
struct SchemaArgs {
    /// Event-schema DSL file (.dwschema). Defaults to the built-in
    /// request/response/error schema.
    #[arg(long, value_name = "FILE")]
    event_schema: Option<PathBuf>,
    /// Provider declarations file (providers.json).
    #[arg(long, value_name = "FILE")]
    providers: Option<PathBuf>,
    /// Macro library file.
    #[arg(long, value_name = "FILE")]
    macros: Option<PathBuf>,
}

#[derive(Subcommand)]
enum Command {
    /// Parse a .dw policy set; report syntax and macro errors only.
    CheckParse {
        /// The .dw policy file (`-` for stdin).
        #[arg(value_name = "POLICIES")]
        policies: PathBuf,
        #[command(flatten)]
        schema: SchemaArgs,
        #[arg(long, value_enum, default_value_t = Format::Human)]
        format: Format,
    },
    /// Parse, lower, and type-check policies against the schema.
    Validate {
        #[arg(value_name = "POLICIES")]
        policies: PathBuf,
        /// The Cedar action schema (.cedarschema).
        #[arg(long, value_name = "FILE")]
        policy_schema: PathBuf,
        #[command(flatten)]
        schema: SchemaArgs,
        #[arg(long, value_enum, default_value_t = Format::Human)]
        format: Format,
    },
    /// Lower a .dw policy set to Cedar; emit policies and the augmented schema.
    Lower {
        #[arg(value_name = "POLICIES")]
        policies: PathBuf,
        #[arg(long, value_name = "FILE")]
        policy_schema: PathBuf,
        #[command(flatten)]
        schema: SchemaArgs,
        /// What to emit.
        #[arg(long, value_enum, default_value_t = Emit::Both)]
        emit: Emit,
        #[arg(long, value_enum, default_value_t = Format::Human)]
        format: Format,
    },
    /// Replay a whole .log event trace; stream per-timepoint verdicts.
    Replay {
        #[arg(value_name = "POLICIES")]
        policies: PathBuf,
        #[arg(long, value_name = "FILE")]
        policy_schema: PathBuf,
        /// The .log event trace.
        #[arg(long, value_name = "FILE")]
        trace: PathBuf,
        #[command(flatten)]
        schema: SchemaArgs,
        #[arg(long, value_enum, default_value_t = Format::Human)]
        format: Format,
    },
    /// Check a single schema artifact on its own, or generate one from MCP.
    Schema {
        #[command(subcommand)]
        what: SchemaCmd,
    },
}

/// The `schema` subcommands — each checks one schema artifact in isolation
/// (so you can tell "my schema is broken" from "my policy is broken"), plus
/// `mcp` which generates a Cedar action schema from an MCP tool manifest.
#[derive(Subcommand)]
enum SchemaCmd {
    /// Check a Cedar action schema (.cedarschema).
    Action {
        /// The .cedarschema file (`-` for stdin).
        #[arg(value_name = "FILE")]
        schema: PathBuf,
        #[arg(long, value_enum, default_value_t = Format::Human)]
        format: Format,
    },
    /// Check an event-schema DSL file (.dwschema).
    Event {
        /// The .dwschema file (`-` for stdin).
        #[arg(value_name = "FILE")]
        schema: PathBuf,
        #[arg(long, value_enum, default_value_t = Format::Human)]
        format: Format,
    },
    /// Check an information-provider declarations file (providers.json).
    Providers {
        /// The providers.json file (`-` for stdin).
        #[arg(value_name = "FILE")]
        providers: PathBuf,
        #[arg(long, value_enum, default_value_t = Format::Human)]
        format: Format,
    },
    /// Generate a Cedar action schema from an MCP `tools/list` manifest.
    Mcp {
        /// The MCP tool manifest (JSON). `-` reads stdin.
        #[arg(long, value_name = "FILE")]
        manifest: PathBuf,
        /// Write the generated .cedarschema here (default: stdout).
        #[arg(short, long, value_name = "FILE")]
        output: Option<PathBuf>,
    },
}

/// What `lower` should emit.
#[derive(Copy, Clone, PartialEq, Eq, ValueEnum)]
enum Emit {
    CedarPolicies,
    CedarSchema,
    /// The augmented schema in Cedar JSON form.
    CedarJson,
    /// Policies + augmented .cedarschema.
    Both,
}

fn main() -> ExitCode {
    match run() {
        Ok(code) => code,
        // A fatal error from an operation: render it and exit 2.
        Err(RunError::Op { error, format }) => {
            render::error(&error, format);
            ExitCode::from(2)
        }
        // A usage/IO problem (file missing, etc.): exit 1.
        Err(RunError::Io(msg)) => {
            eprintln!("error: {msg}");
            ExitCode::from(1)
        }
    }
}

/// A run either succeeds (with the process exit code the command chose) or
/// fails with a fatal operation error (exit 2) or an IO/usage error (exit 1).
enum RunError {
    Op { error: OpError, format: Format },
    Io(String),
}

fn run() -> Result<ExitCode, RunError> {
    let cli = Cli::parse();
    match cli.command {
        Command::CheckParse {
            policies,
            schema,
            format,
        } => {
            let src = read(&policies)?;
            let owned = OwnedSchema::load(&schema)?;
            let report = ops::check_parse(&src, &owned.inputs()).map_err(op_err(format))?;
            render::check_parse(&report, format);
            Ok(ExitCode::SUCCESS)
        }
        Command::Validate {
            policies,
            policy_schema,
            schema,
            format,
        } => {
            let src = read(&policies)?;
            let action_schema = read(&policy_schema)?;
            let owned = OwnedSchema::load(&schema)?;
            let report = ops::validate_policies(&src, &owned.inputs(), &action_schema)
                .map_err(op_err(format))?;
            render::validate(&report, format);
            // Validation errors are a non-fatal channel; a failing validation
            // is still exit 2 (input rejected), a clean one exit 0.
            Ok(if report.passed {
                ExitCode::SUCCESS
            } else {
                ExitCode::from(2)
            })
        }
        Command::Lower {
            policies,
            policy_schema,
            schema,
            emit,
            format,
        } => {
            let src = read(&policies)?;
            let action_schema = read(&policy_schema)?;
            let owned = OwnedSchema::load(&schema)?;
            let artifacts = ops::lower_to_cedar(&src, &owned.inputs(), &action_schema)
                .map_err(op_err(format))?;
            render::lower(&artifacts, emit, format);
            Ok(ExitCode::SUCCESS)
        }
        Command::Replay {
            policies,
            policy_schema,
            trace,
            schema,
            format,
        } => {
            let src = read(&policies)?;
            let action_schema = read(&policy_schema)?;
            let log = read(&trace)?;
            let owned = OwnedSchema::load(&schema)?;
            let report = ops::replay_trace(&src, &owned.inputs(), &action_schema, &log)
                .map_err(op_err(format))?;
            render::replay(&report, format);
            Ok(ExitCode::SUCCESS)
        }
        Command::Schema { what } => run_schema(what),
    }
}

/// Handle the `schema` subcommands.
fn run_schema(what: SchemaCmd) -> Result<ExitCode, RunError> {
    match what {
        SchemaCmd::Action { schema, format } => {
            let src = read(&schema)?;
            let report = ops::check_action_schema(&src).map_err(op_err(format))?;
            render::schema_check(&report, format);
            Ok(ExitCode::SUCCESS)
        }
        SchemaCmd::Event { schema, format } => {
            let src = read(&schema)?;
            let report = ops::check_event_schema(&src).map_err(op_err(format))?;
            render::schema_check(&report, format);
            Ok(ExitCode::SUCCESS)
        }
        SchemaCmd::Providers { providers, format } => {
            let src = read(&providers)?;
            let report = ops::check_providers(&src).map_err(op_err(format))?;
            render::schema_check(&report, format);
            Ok(ExitCode::SUCCESS)
        }
        SchemaCmd::Mcp { manifest, output } => {
            let src = read(&manifest)?;
            // A fatal generation error renders in human form (no --format here).
            let schema = ops::generate_mcp_schema(&src).map_err(op_err(Format::Human))?;
            match output {
                Some(path) => std::fs::write(&path, &schema)
                    .map_err(|e| RunError::Io(format!("writing {}: {e}", path.display())))?,
                None => print!("{schema}"),
            }
            Ok(ExitCode::SUCCESS)
        }
    }
}

/// Curry the output format into the error path so a fatal error is rendered in
/// the requested format.
fn op_err(format: Format) -> impl FnOnce(OpError) -> RunError {
    move |error| RunError::Op { error, format }
}

/// The service-schema override file contents, read to owned `String`s so they
/// outlive the borrowed [`SchemaInputs`] handed to the ops functions.
struct OwnedSchema {
    event_schema: Option<String>,
    providers: Option<String>,
    macros: Option<String>,
}

impl OwnedSchema {
    fn load(args: &SchemaArgs) -> Result<Self, RunError> {
        Ok(OwnedSchema {
            event_schema: args.event_schema.as_deref().map(read).transpose()?,
            providers: args.providers.as_deref().map(read).transpose()?,
            macros: args.macros.as_deref().map(read).transpose()?,
        })
    }

    fn inputs(&self) -> SchemaInputs<'_> {
        SchemaInputs {
            event_schema: self.event_schema.as_deref(),
            providers: self.providers.as_deref(),
            macros: self.macros.as_deref(),
        }
    }
}

/// Read a file to a `String`, or stdin when the path is `-`.
fn read(path: &std::path::Path) -> Result<String, RunError> {
    if path.as_os_str() == "-" {
        use std::io::Read;
        let mut buf = String::new();
        std::io::stdin()
            .read_to_string(&mut buf)
            .map_err(|e| RunError::Io(format!("reading stdin: {e}")))?;
        Ok(buf)
    } else {
        std::fs::read_to_string(path)
            .map_err(|e| RunError::Io(format!("reading {}: {e}", path.display())))
    }
}
