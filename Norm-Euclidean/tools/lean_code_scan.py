import re


def code_without_comments(source: str) -> str:
    """Preserve line numbers while excluding Lean nested and line comments and strings."""
    result = []
    index = 0
    depth = 0
    line_comment = False
    string = False
    while index < len(source):
        char = source[index]
        pair = source[index:index + 2]
        if line_comment:
            result.append('\n' if char == '\n' else ' ')
            line_comment = char != '\n'
            index += 1
        elif depth:
            if pair == '/-':
                depth += 1
                result.extend('  ')
                index += 2
            elif pair == '-/':
                depth -= 1
                result.extend('  ')
                index += 2
            else:
                result.append('\n' if char == '\n' else ' ')
                index += 1
        elif string:
            if char == '\\' and index + 1 < len(source):
                result.extend('  ')
                index += 2
            else:
                result.append('\n' if char == '\n' else ' ')
                string = char != '"'
                index += 1
        elif pair == '--':
            result.extend('  ')
            line_comment = True
            index += 2
        elif pair == '/-':
            result.extend('  ')
            depth = 1
            index += 2
        elif char == '"':
            result.append(' ')
            string = True
            index += 1
        else:
            result.append(char)
            index += 1
    assert depth == 0 and not string, 'Unterminated source comment or string'
    return ''.join(result)


def violations(source: str) -> list[int]:
    return [line_no for line_no, line in enumerate(code_without_comments(source).splitlines(), 1)
            if re.search(r'\b(sorry|sorryAx|admit)\b|^\s*'
                         r'(?:(?:private|public|protected)\s+)*(?:axiom|constant)\b', line)]
