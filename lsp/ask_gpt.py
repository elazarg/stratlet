"""
Send a query to ChatGPT and print the response.

Usage:
    python lsp/ask_gpt.py <query_file> [--system <system_file>] [--model MODEL] [--max-tokens N]

The query file contains the user prompt. An optional system file contains the system prompt.
Reads OPENAI_API_KEY from .env in the project root.
"""

import argparse
import json
import os
import pathlib
import urllib.request

PROJECT_ROOT = pathlib.Path(__file__).resolve().parent.parent


def load_env():
    """Load .env file into os.environ."""
    env_file = PROJECT_ROOT / ".env"
    if env_file.exists():
        for line in env_file.read_text().splitlines():
            line = line.strip()
            if line and not line.startswith("#") and "=" in line:
                key, val = line.split("=", 1)
                os.environ.setdefault(key.strip(), val.strip())


def ask(user_prompt: str, system_prompt: str = "", model: str = "gpt-5.2", max_tokens: int = 3000) -> str:
    api_key = os.environ.get("OPENAI_API_KEY")
    if not api_key:
        return "ERROR: OPENAI_API_KEY not set"

    messages = []
    if system_prompt:
        messages.append({"role": "system", "content": system_prompt})
    messages.append({"role": "user", "content": user_prompt})

    # Newer models (gpt-5.x) require max_completion_tokens; older ones use max_tokens
    token_param = "max_completion_tokens" if model.startswith("gpt-5") else "max_tokens"
    data = json.dumps({
        "model": model,
        "messages": messages,
        token_param: max_tokens,
        "temperature": 0.2,
    }).encode()

    req = urllib.request.Request(
        "https://api.openai.com/v1/chat/completions",
        data=data,
        headers={
            "Content-Type": "application/json",
            "Authorization": f"Bearer {api_key}",
        },
    )

    try:
        resp = urllib.request.urlopen(req, timeout=120)
    except urllib.error.HTTPError as e:
        body = e.read().decode("utf-8", errors="replace")
        return f"ERROR {e.code}: {body}"

    result = json.loads(resp.read())
    return result["choices"][0]["message"]["content"]


def main():
    parser = argparse.ArgumentParser(description="Ask ChatGPT")
    parser.add_argument("query_file", help="File containing the user prompt")
    parser.add_argument("--system", help="File containing system prompt", default=None)
    parser.add_argument("--model", default="gpt-5.2")
    parser.add_argument("--max-tokens", type=int, default=3000)
    args = parser.parse_args()

    load_env()

    user_prompt = pathlib.Path(args.query_file).read_text(encoding="utf-8")
    system_prompt = ""
    if args.system:
        system_prompt = pathlib.Path(args.system).read_text(encoding="utf-8")

    result = ask(user_prompt, system_prompt, args.model, args.max_tokens)
    # Handle Windows console encoding
    import sys
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")
    print(result)


if __name__ == "__main__":
    main()
