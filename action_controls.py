"""Traverse executable branches without depending on the GUI."""


def if_scope_label(number, name):
    return f"#{number}" + (f" {name}" if name else "")


def walk_actions(actions, blocked=False):
    for action in actions:
        yield action, blocked
        child_blocked = blocked or not action.enabled
        yield from walk_actions(action.actions, child_blocked)
        for block in action.elif_blocks:
            condition, children = block[:2]
            yield from walk_actions(children, child_blocked or not condition.enabled)
        yield from walk_actions(action.else_actions, child_blocked or not action.else_enabled)


def macro_actions(macro):
    yield from walk_actions(macro.actions)
    yield from walk_actions(macro.stop_actions)
