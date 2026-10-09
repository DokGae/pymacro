import tempfile
import unittest
import wave
from pathlib import Path
from unittest.mock import Mock, patch

import capture
from capture import ScreenCaptureManager


class CaptureSoundTests(unittest.TestCase):
    def test_shutter_asset_and_async_playback(self):
        path = Path(capture.__file__).parent / 'assets' / 'shutter.wav'
        with wave.open(str(path)) as sound:
            self.assertGreater(sound.getnframes(), 0)
            self.assertLess(sound.getnframes() / sound.getframerate(), 1)
        backend = Mock(SND_FILENAME=1, SND_ASYNC=2, SND_NODEFAULT=4)
        with patch.object(capture, 'winsound', backend):
            capture._play_shutter()
        backend.PlaySound.assert_called_once_with(str(path), 7)
        backend.PlaySound.side_effect = RuntimeError('audio unavailable')
        with patch.object(capture, 'winsound', backend):
            capture._play_shutter()

    def test_single_capture_sounds_for_screen_and_window(self):
        for target in (None, {'process_name': 'game.exe'}):
            with self.subTest(target=target), tempfile.TemporaryDirectory() as root:
                manager = ScreenCaptureManager(output_dir=root, image_format='png')
                manager.window_target = target
                sct = Mock(monitors=[{'left': 0, 'top': 0, 'width': 2, 'height': 2}])
                sct.grab.return_value = Mock(rgb=bytes(12), size=(2, 2))
                with patch('capture.mss.mss') as factory, patch('capture.target_client_region', return_value=(0, 0, 2, 2)), patch('capture._play_shutter') as play:
                    factory.return_value.__enter__.return_value = sct
                    self.assertTrue(manager.capture_once().exists())
                    play.assert_called_once()

    def test_failed_capture_does_not_sound(self):
        with tempfile.TemporaryDirectory() as root:
            manager = ScreenCaptureManager(output_dir=root)
            with patch.object(manager, '_grab_frame', side_effect=RuntimeError('capture failed')), patch('capture._play_shutter') as play:
                with self.assertRaises(RuntimeError):
                    manager.capture_once()
                play.assert_not_called()

    def test_continuous_capture_sounds_only_on_first_saved_frame(self):
        with tempfile.TemporaryDirectory() as root:
            manager = ScreenCaptureManager(output_dir=root, image_format='png')
            for seq in (1, 2):
                manager._enqueue_frame((seq, '', bytes(12), (2, 2), {}))
            manager._writer_stop.set()
            with patch('capture._play_shutter') as play:
                manager._writer_loop()
                play.assert_called_once()
            self.assertEqual(len(list(Path(root).glob('*.png'))), 2)
