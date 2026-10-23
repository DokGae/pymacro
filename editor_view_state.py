"""JSON-safe editor presentation state; kept separate from macro execution data."""
from PyQt6 import QtCore


def editor_trees(dialog):
    return (dialog.main_action_tree, dialog.parallel_action_tree, dialog.stop_action_tree)


def _json_view(view):
    return {**view, 'expanded': [list(path) for path in sorted(view['expanded'])]}


def collect_editor_view(dialog):
    trees = []
    for tree in editor_trees(dialog):
        view = _json_view(tree.view_state())
        view.update(hide_disabled=tree._hide_disabled,
                    horizontal_scroll=tree.horizontalScrollBar().value(),
                    columns=[tree.columnWidth(i) for i in range(tree.columnCount())],
                    focus=list(tree._item_path_key(tree._focus_item)) if tree._focus_item else None,
                    focus_view=_json_view(tree._focus_view) if tree._focus_view else None)
        trees.append(view)
    size = dialog.normalGeometry().size() if dialog.isMaximized() else dialog.size()
    return dict(size=[size.width(), size.height()], maximized=dialog.isMaximized(),
                geometry=bytes(dialog.saveGeometry().toHex()).decode(),
                tab=dialog.action_tabs.currentIndex(), trees=trees)


def _restore_tree(tree, view):
    expanded = {tuple(path) for path in view.get('expanded', [])}
    tree.restore_view(dict(expanded=expanded, current=view.get('current'),
                           selected=view.get('selected', []), scroll=view.get('scroll', 0)))
    focus = tree.at_path(view.get('focus'))
    if focus is not None and tree.is_if(focus):
        current = tree.currentItem()
        tree.setCurrentItem(focus)
        tree.toggle_focus()
        if current is not None:
            tree.setCurrentItem(current)
        focus_view = view.get('focus_view')
        if focus_view:
            tree._focus_view = {**focus_view, 'expanded': {tuple(p) for p in focus_view['expanded']}}
    tree.refresh_workspace()
    tree.verticalScrollBar().setValue(view.get('scroll', 0))
    tree.horizontalScrollBar().setValue(view.get('horizontal_scroll', 0))


def restore_editor_view(dialog, state, *, restore_tree_views=True):
    if state.get('geometry'):
        dialog.restoreGeometry(QtCore.QByteArray.fromHex(state['geometry'].encode()))
    elif state.get('size'):
        dialog.resize(*state['size'])
    if state.get('maximized'):
        dialog.setWindowState(dialog.windowState() | QtCore.Qt.WindowState.WindowMaximized)
    dialog.action_tabs.setCurrentIndex(max(0, min(dialog.action_tabs.count() - 1, state.get('tab', 0))))
    for tree, view in zip(editor_trees(dialog), state.get('trees', [])):
        tree.hide_disabled_button.setChecked(bool(view.get('hide_disabled', False)))
        for index, width in enumerate(view.get('columns', [])[:tree.columnCount()]):
            tree.setColumnWidth(index, width)
        if restore_tree_views:
            _restore_tree(tree, view)

