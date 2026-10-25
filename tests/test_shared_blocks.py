"""Reusable definitions, runner isolation and real editor operations (no input driver)."""
import copy
import json
import unittest
from pathlib import Path
from unittest.mock import patch

from PyQt6 import QtCore, QtWidgets
from engine import Action, Condition, Macro, MacroProfile, MacroRunner
from main import MacroDialog, ActionEditDialog
from lib.shared_blocks import expand_actions, register, validate, usages
from test_execution_analysis import APP, make_runner


def pump():
    for _ in range(4):
        APP.processEvents()


class SharedBlockTests(unittest.TestCase):
    def test_roundtrip_branches_and_original_are_not_expanded(self):
        entries = {}
        ref = register(entries, '침투', [Action(type='if', condition=Condition(type='key', key='a'),
                       actions=[Action(type='press', key='x')], else_actions=[Action(type='press', key='y')],
                       elif_blocks=[(Condition(type='key', key='b'), [Action(type='noop')], 'B')],
                       transition_actions=[Action(type='up', key='x')]).to_dict()])
        call = Action(type='shared_block', block_ref=ref)
        profile = MacroProfile(shared_blocks=entries, macros=[Macro(trigger_key='z', actions=[call], stop_actions=[copy.deepcopy(call)])])
        restored = MacroProfile.from_dict(json.loads(json.dumps(profile.to_dict())))
        self.assertEqual(restored.to_dict(), profile.to_dict())
        expanded = expand_actions([call.to_dict(), call.to_dict()], entries)
        self.assertEqual(len(expanded[0]['actions'][0]['elif_blocks']), 1)
        expanded[0]['actions'][0]['actions'].clear()
        self.assertEqual(len(expanded[1]['actions'][0]['actions']), 1)
        self.assertEqual(call.actions, [])
        self.assertEqual(len(usages([m.to_dict() for m in profile.macros], entries, ref)), 2)

    def test_invalid_links_cycles_and_nested_parallel_are_rejected(self):
        with self.assertRaisesRegex(ValueError, '찾을 수'):
            expand_actions([{'type': 'shared_block', 'block_ref': 'missing'}], {})
        entries = {'a': {'name': 'A', 'actions': [{'type': 'shared_block', 'block_ref': 'b'}]},
                   'b': {'name': 'B', 'actions': [{'type': 'shared_block', 'block_ref': 'a'}]}}
        with self.assertRaisesRegex(ValueError, '순환'):
            validate(entries)
        with self.assertRaisesRegex(ValueError, '병렬'):
            validate({'a': {'name': 'A', 'actions': [Action(type='group', parallel_enabled=True).to_dict()]}})

    def test_runner_evaluates_each_call_and_snapshots_definition(self):
        _, engine = make_runner([], outcomes=[True, False])
        engine._profile.shared_blocks = {'a': {'name': '처리', 'actions': [Action(type='if',
            condition=Condition(type='key', key='a'), actions=[Action(type='press', key='x')],
            else_actions=[Action(type='press', key='y')]).to_dict()]}}
        macro = Macro(trigger_key='z', actions=[Action(type='shared_block', block_ref='a'), Action(type='shared_block', block_ref='a')])
        runner = MacroRunner(macro, engine, 0)
        runner._current_cycle = 0
        engine._profile.shared_blocks['a']['actions'] = [Action(type='press', key='z').to_dict()]
        result = runner._run_actions(runner.macro.actions, {}, root=True)
        self.assertEqual(result.signal, 'none')
        self.assertEqual([call.args[1] for call in engine._send_key.call_args_list], ['x', 'y'])
        self.assertEqual(macro.actions[0].actions, [])
        next_run = MacroRunner(macro, engine, 0)
        self.assertEqual(next_run.macro.actions[0].actions[0].key, 'z')

    def test_control_flow_propagates_and_disabled_call_skips(self):
        for signal in ('return', 'continue', 'break', 'goto'):
            _, engine = make_runner([])
            engine._profile.shared_blocks = {'a': {'name': '분기', 'actions': [Action(type=signal, goto_label='end').to_dict()]}}
            macro = Macro(trigger_key='z', actions=[Action(type='shared_block', block_ref='a')])
            runner = MacroRunner(macro, engine)
            runner._current_cycle = 0
            result = runner._exec_action(runner.macro.actions[0], {}, [], [0])
            self.assertEqual(result.signal, signal)
            runner.macro.actions[0].enabled = False
            self.assertEqual(runner._exec_action(runner.macro.actions[0], {}, [], [0]).signal, 'none')

    def test_existing_assassin_profile_still_loads_without_conversion(self):
        if not Path('setting/암극(살성).json').exists():
            self.skipTest('사용자 프로필이 없는 환경')
        data = json.loads(Path('setting/암극(살성).json').read_text(encoding='utf-8'))
        profile = MacroProfile.from_dict(data)
        self.assertEqual(profile.shared_blocks, data.get('shared_blocks', {}))
        from lib.shared_blocks import walk
        before = [a.get('block_ref') for _, a in walk(data['macros'][0]['actions']) if a['type'] == 'shared_block']
        after = [a.get('block_ref') for _, a in walk(profile.macros[0].to_dict()['actions']) if a['type'] == 'shared_block']
        self.assertEqual(before, after)

    def test_nested_calls_and_stop_actions_have_independent_expansions(self):
        _, engine = make_runner([])
        engine._profile.shared_blocks = {
            'leaf': {'name': '입력', 'actions': [Action(type='press', key='x').to_dict()]},
            'outer': {'name': '묶음', 'actions': [Action(type='shared_block', block_ref='leaf').to_dict()]}}
        macro = Macro(trigger_key='z', actions=[Action(type='shared_block', block_ref='outer')],
                      stop_actions=[Action(type='shared_block', block_ref='outer')])
        runner = MacroRunner(macro, engine)
        runner._current_cycle = 0
        runner._run_actions(runner.macro.actions, {})
        runner._running_stop_actions = True
        runner._stop_event.set()
        runner._run_actions(runner.macro.stop_actions, {})
        self.assertEqual(engine._send_key.call_count, 2)
        self.assertIsNot(runner.macro.actions[0].actions[0], runner.macro.stop_actions[0].actions[0])


class SharedBlockEditorTests(unittest.TestCase):
    def setUp(self):
        self.previous_clipboard = MacroDialog._action_clipboard
        self.owner = QtWidgets.QWidget()
        self.owner.profile = MacroProfile()
        self.dialog = MacroDialog(self.owner, macro=Macro(name='new', trigger_key='z', actions=[
            Action(type='if', name='침투', condition=Condition(type='key', key='a'),
                   actions=[Action(type='press', key='x')]), Action(type='sleep', sleep_ms=10)]))
        self.dialog.resize(1500, 900)
        self.dialog.show()
        self.blocks = self.dialog.block_workspace
        self.tree = self.dialog.main_action_tree
        pump()

    def tearDown(self):
        MacroDialog._action_clipboard = self.previous_clipboard
        pump()
        self.dialog.close()
        self.owner.close()
        self.owner.deleteLater()
        QtCore.QCoreApplication.sendPostedEvents(None, QtCore.QEvent.Type.DeferredDelete)
        pump()

    def make_block(self):
        self.tree.setCurrentItem(self.tree.topLevelItem(0))
        with patch.object(self.blocks, 'prompt', side_effect=lambda title, initial, callback: callback('침투 처리')):
            self.blocks.make_shared()
        return next(iter(self.blocks.entries))

    def test_wrap_copy_rename_detach_and_undo_restore_definitions(self):
        ref = self.make_block()
        self.assertEqual(self.tree.collect_actions()[0].block_ref, ref)
        self.assertFalse(self.owner.profile.shared_blocks)
        self.dialog._copy_action(self.tree)
        self.dialog._paste_action(self.tree)
        self.assertEqual([a.block_ref for a in self.tree.collect_actions()[:2]], [ref, ref])
        self.blocks.open(ref, True)
        self.blocks.name.setText('새 이름')
        self.blocks.save_definition()
        self.blocks.flush()
        self.assertEqual([a.name for a in self.tree.collect_actions()[:2]], ['새 이름', '새 이름'])
        self.tree.setCurrentItem(self.tree.topLevelItem(0))
        self.blocks.detach(tree=self.tree)
        actions = self.tree.collect_actions()
        self.assertEqual(actions[0].type, 'group')
        self.assertEqual(actions[0].actions[0].name, '침투')
        self.assertEqual(actions[1].block_ref, ref)
        self.dialog.action_history.undo()
        self.assertEqual(self.tree.collect_actions()[0].block_ref, ref)
        self.dialog.action_history.undo()
        self.assertEqual(self.blocks.entries[ref]['name'], '침투 처리')

    def test_wrap_undo_redo_and_cancel_do_not_modify_profile(self):
        self.make_block()
        self.dialog.action_history.undo()
        self.assertFalse(self.blocks.entries)
        self.assertEqual(self.tree.collect_actions()[0].type, 'if')
        self.dialog.action_history.redo()
        self.assertEqual(self.tree.collect_actions()[0].type, 'shared_block')
        self.dialog.reject()
        self.assertFalse(self.owner.profile.shared_blocks)

    def test_edit_definition_uses_existing_editor_and_readonly_preview(self):
        ref = self.make_block()
        self.assertFalse(self.blocks.editing)
        self.blocks.open(ref, True)
        self.blocks.tree.load_actions([Action(type='sleep', sleep_ms=123)])
        pump()
        self.assertEqual(self.blocks.entries[ref]['actions'][0]['sleep_ms'], 123)
        self.dialog.get_macro()
        self.blocks.open(ref, False)
        self.assertFalse(self.blocks.tree.topLevelItem(0).flags() & QtCore.Qt.ItemFlag.ItemIsUserCheckable)

    def test_delete_in_use_and_missing_clipboard_reference_are_blocked(self):
        ref = self.make_block()
        self.blocks.delete()
        self.assertIn(ref, self.blocks.entries)
        MacroDialog._action_clipboard = [Action(type='shared_block', block_ref='missing')]
        before = self.tree.collect_actions()
        self.dialog._paste_action(self.tree)
        self.assertEqual(self.tree.collect_actions(), before)

    def test_stop_tab_still_targets_stop_tree(self):
        self.dialog.action_tabs.setCurrentWidget(self.dialog.stop_group)
        self.assertIs(self.dialog.action_tree, self.dialog.stop_action_tree)

    def test_exact_duplicate_review_excludes_different_conditions_and_undoes(self):
        original = self.tree.collect_actions()[0]
        variant = copy.deepcopy(original)
        variant.condition.key = 'b'
        self.tree.load_actions([original, copy.deepcopy(original), variant])
        ref = self.make_block()
        review = next(d for d in self.dialog.findChildren(QtWidgets.QDialog) if d.isVisible() and d.windowTitle().startswith('동일한 묶음 검토'))
        self.assertTrue(review.isVisible())
        listing = review.findChild(QtWidgets.QListWidget)
        self.assertEqual(listing.count(), 1)
        self.assertIn('new / 일반 액션', listing.item(0).text())
        listing.item(0).setCheckState(QtCore.Qt.CheckState.Checked)
        next(b for b in review.findChildren(QtWidgets.QPushButton) if b.text().startswith('선택한 위치를')).click()
        actions = self.tree.collect_actions()
        self.assertEqual([a.block_ref for a in actions[:2]], [ref, ref])
        self.assertEqual(actions[2].condition.key, 'b')
        self.dialog.action_history.undo()
        self.assertEqual(self.tree.collect_actions()[1].type, 'if')

    def test_pasting_self_reference_into_definition_is_rejected(self):
        ref = self.make_block()
        self.blocks.open(ref, True)
        self.blocks.tree.setCurrentItem(self.blocks.tree.topLevelItem(0))
        MacroDialog._action_clipboard = [Action(type='shared_block', block_ref=ref)]
        original = self.blocks.tree.collect_actions()
        self.dialog._paste_action(self.blocks.tree)
        self.assertEqual(original, self.blocks.tree.collect_actions())

    def test_preview_is_explicit_and_stays_closed_after_selection_and_undo(self):
        ref = self.make_block()
        self.assertTrue(self.blocks.panel.isHidden())
        self.tree.setCurrentItem(self.tree.topLevelItem(1))
        self.tree.setCurrentItem(self.tree.topLevelItem(0))
        pump()
        self.assertTrue(self.blocks.panel.isHidden())
        self.blocks.preview_selected()
        self.assertFalse(self.blocks.panel.isHidden())
        self.assertFalse(self.blocks.editing)
        self.blocks.panel.hide()
        self.blocks.list.setCurrentRow(0)
        self.assertTrue(self.blocks.panel.isHidden())
        self.dialog.action_history.undo()
        self.dialog.action_history.redo()
        self.assertTrue(self.blocks.panel.isHidden())
        self.assertIn(ref, self.blocks.entries)

    def test_action_columns_are_manually_resizable_and_survive_refresh(self):
        for tree in (*self.blocks.source_trees, self.blocks.tree):
            for column in range(tree.columnCount()):
                self.assertEqual(tree.header().sectionResizeMode(column), QtWidgets.QHeaderView.ResizeMode.Interactive)
            tree.header().resizeSection(0, 90)
            tree.header().resizeSection(1, 220)
            tree.header().resizeSection(3, 480)
            tree.refresh_workspace()
            self.assertEqual([tree.columnWidth(i) for i in (0, 1, 3)], [90, 220, 480])

    def test_shared_block_is_added_through_normal_action_kind(self):
        ref = self.make_block()
        def configure(dialog):
            dialog.type_combo.setCurrentIndex(dialog.type_combo.findData('shared_block'))
            dialog.show()
            pump()
            self.assertTrue(dialog.block_target_combo.isVisible())
            self.assertTrue(dialog.primary_section.isVisible())
            with self.assertRaises(ValueError):
                dialog.get_action()
            dialog.block_target_combo.setCurrentIndex(dialog.block_target_combo.findData(ref))
            self.assertEqual(dialog.get_action().block_ref, ref)
            dialog.hide()
            return 1
        self.tree.setCurrentItem(self.tree.topLevelItem(1))
        with patch('main._run_dialog_non_modal', side_effect=configure):
            self.dialog._add_action()
        self.assertEqual(self.tree.collect_actions()[-1].block_ref, ref)

    def test_repeat_search_uses_clicked_block_and_named_location(self):
        original = copy.deepcopy(self.tree.collect_actions()[0])
        ref = self.make_block()
        self.tree._append_action_item(original)
        self.blocks.active = None
        self.blocks.find_matches(reference=ref)
        review = next(d for d in self.dialog.findChildren(QtWidgets.QDialog) if d.isVisible() and d.windowTitle().startswith('동일한 묶음 검토'))
        listing = review.findChild(QtWidgets.QListWidget)
        self.assertEqual(listing.count(), 1)
        self.assertIn('침투', listing.item(0).text())
        self.assertNotIn('→', listing.item(0).text())
        listing.setCurrentRow(0)
        next(b for b in review.findChildren(QtWidgets.QPushButton) if b.text() == '선택한 위치 보기').click()
        self.assertIs(self.tree.currentItem(), self.tree.topLevelItem(2))

    def test_library_summary_details_and_double_click_preview(self):
        self.assertEqual(self.dialog.action_tabs.tabText(2), '공용 블록 (0)')
        self.assertFalse(self.blocks.entry_buttons[0].isEnabled())
        ref = self.make_block()
        self.assertEqual(self.dialog.action_tabs.tabText(2), '공용 블록 (1)')
        self.assertIn('연결 1곳', self.blocks.overview.text())
        self.assertIn('IF 1개', self.blocks.detail_description.text())
        self.assertEqual(self.blocks.detail_tree.topLevelItem(0).text(0), '침투')
        self.assertIn('new', self.blocks.detail_usages.text())
        self.assertTrue(self.blocks.panel.isHidden())
        self.blocks.list.itemDoubleClicked.emit(self.blocks.list.item(0))
        self.assertFalse(self.blocks.panel.isHidden())
        self.assertFalse(self.blocks.editing)
        self.assertEqual(self.blocks.active, ref)
        self.blocks.search.setText('검색결과없음')
        self.assertEqual(self.dialog.action_tabs.tabText(2), '공용 블록 (1)')
        self.assertFalse(self.blocks.empty_hint.isHidden())

    def test_additional_timer_condition_is_not_an_identical_block(self):
        from lib.shared_blocks import fingerprint
        source = Action(type='if', name='침투', condition=Condition(type='all', conditions=[Condition(type='key', key='a')]))
        variant = copy.deepcopy(source)
        variant.condition.conditions.append(Condition(type='timer', timer_index=1, timer_value=1, timer_operator='ge'))
        self.assertNotEqual(fingerprint([source.to_dict()]), fingerprint([variant.to_dict()]))


if __name__ == '__main__':
    unittest.main()
