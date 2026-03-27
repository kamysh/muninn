use clap::Parser;

#[derive(Parser)]
#[command(name = "ai-mem", about = "ai-mem repository index manager")]
struct Cli {}

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    let _cli = Cli::parse();
    Ok(())
}