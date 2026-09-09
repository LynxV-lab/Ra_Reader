import tkinter as tk
from tkinter import (
    Canvas,
    Scrollbar,
    Frame,
    Text,
    Menu,
    filedialog,
    simpledialog,
    colorchooser,
    ttk
)
import tkinter.font as tkfont

from PIL import (
    Image,
    ImageTk,
    ImageDraw,
    ImageFont
)

import json
import os
import re
import bisect
import base64
import io
import html
import sys
import subprocess
import unicodedata
import mimetypes
from email import policy
from email.parser import BytesParser
from html.parser import HTMLParser
import difflib
import shlex

from pathlib import Path
from datetime import datetime
import xml.etree.ElementTree as ET


class RaReader:
    FADE_FRAMES = 10
    FADE_DELAY = 25
    CLICK_OFFSET = 2
    CLICK_DELAY = 100

    APP_TITLE = 'Ra_Reader'

    TOP_BAR_HEIGHT = 45
    BOTTOM_BAR_HEIGHT = 50

    READER_TOP_PADDING = 10
    READER_BOTTOM_PADDING = 8

    READER_HORIZONTAL_PADDING_MIN = 50
    READER_TEXT_MAX_WIDTH = 1000

    READER_MIN_GAP = 4
    READER_LAST_PAGE_GAP = 6
    READER_BOTTOM_SAFETY = 8

    # =========================================================
    # Bottom reader bar
    # =========================================================

    FILL_X = 90
    PREV_BOOKMARK_X = 122
    NEXT_BOOKMARK_X = 154
    BOOKMARK_X = 186

    BOTTOM_BUTTON_Y = (
        BOTTOM_BAR_HEIGHT - 20
    )

    LINE_LEFT = 228
    LINE_RIGHT_MARGIN = 70

    LINE_Y = (
        BOTTOM_BAR_HEIGHT - 18
    )

    BOTTOM_TEXT_Y = (
        BOTTOM_BAR_HEIGHT - 8
    )

    # =========================================================
    # Top bar
    # =========================================================

    TOP_ICON_Y = 20

    THEME_UNDERLINE_TOP = 33
    THEME_UNDERLINE_Y = (
        THEME_UNDERLINE_TOP + 1
    )

    # =========================================================
    # Continue
    # =========================================================

    CONTINUE_Y = 20
    CONTINUE_WIDTH = 214
    CONTINUE_HEIGHT = 30

    # =========================================================
    # Highlight
    # =========================================================

    HIGHLIGHT_COLOR = '#ffb2b2'

    # =========================================================
    # Reader search
    # =========================================================

    SEARCH_NORMAL_COLOR = '#00ff03'
    SEARCH_CURRENT_COLOR = '#009501'

    SEARCH_MIN_CHARS = 2
    SEARCH_BOX_WIDTH = 476
    SEARCH_BOX_NARROW_WIDTH = 146

    SEARCH_BOX_HEIGHT = 30
    SEARCH_BOX_TOP = 5

    SEARCH_TEXT_LEFT = 20
    SEARCH_TEXT_RIGHT = 20

    SEARCH_ICON_SIZE = 24
    SEARCH_ICON_FIRST_GAP = 6
    SEARCH_ICON_GAP = 8
    SEARCH_COLLISION_GAP = 8

    SEARCH_MARKER_WIDTH = 4
    SEARCH_MARKER_HEIGHT = 18
    SEARCH_MARKER_COLOR = '#009501'

    # Текущее найденное совпадение стараемся
    # показывать на 7-й визуальной строке.
    SEARCH_TARGET_VISUAL_LINE = 7

    # =========================================================
    # Projects
    # =========================================================

    PROJECT_NUMBER_GAP = 28
    PROJECT_NUMBER_RAISE = 14

    # =========================================================
    # Global search
    # =========================================================

    GLOBAL_SEARCH_Y = 112

    GLOBAL_CHECKBOX_Y = 158
    GLOBAL_CHECKBOX_SIZE = 24
    GLOBAL_CHECKBOX_TEXT_GAP = 6
    GLOBAL_CHECKBOX_GROUP_GAP = 26

    GLOBAL_RESULT_TITLE_WIDTH = 360
    GLOBAL_RESULT_TEXT_WIDTH = 600
    GLOBAL_RESULT_HEIGHT = 200
    GLOBAL_RESULT_GAP = 70

    GLOBAL_RESULT_VERTICAL_GAP = 8

    GLOBAL_RESULT_BORDER = '#306263'
    GLOBAL_RESULT_BORDER_WIDTH = 1

    GLOBAL_RESULTS_TOP = 196
    GLOBAL_RESULTS_BOTTOM_PADDING = 20

    GLOBAL_RESULTS_PER_PAGE = 50

    # =========================================================
    # Notes
    # =========================================================

    NOTES_TOP_MARGIN = 40
    NOTES_BOTTOM_MARGIN = 40

    NOTES_CONTROL_LEFT = 8
    NOTES_CONTROL_BOTTOM = 8
    NOTES_CONTROL_GAP = 8

    NOTES_TAB_HEIGHT = 30
    NOTES_TAB_GAP = 2

    NOTES_MAX_SHEETS = 10

    NOTES_AUTOSAVE_DELAY = 5000

    # =========================================================
    # Themes
    # =========================================================

    THEMES = {
        'day': {
            'background': '#ffffff',
            'text': '#000000',
            'secondary': '#555555',
            'line': '#d0d0d0',
        },

        'sepia': {
            'background': '#e3e4c9',
            'text': '#2d2d2d',
            'secondary': '#555555',
            'line': '#bfc0aa',
        },

        'night': {
            'background': '#000000',
            'text': '#eaeaea',
            'secondary': '#aaaaaa',
            'line': '#444444',
        }
    }

    def __init__(self):
        self.root = tk.Tk()

        self.root.title(
            self.APP_TITLE
        )

        # =====================================================
        # Base directory
        #
        # Обычный запуск:
        # каталог .py
        #
        # PyInstaller:
        # каталог .exe
        # =====================================================

        if getattr(
            sys,
            'frozen',
            False
        ):
            base_dir = (
                Path(
                    sys.executable
                ).resolve().parent
            )
        else:
            base_dir = (
                Path(
                    __file__
                ).resolve().parent
            )

        self.base_dir = base_dir

        appdata = os.getenv(
            'APPDATA'
        )

        if appdata:
            self.config_dir = (
                Path(appdata)
                / 'Ra_Reader'
            )

        else:
            self.config_dir = (
                Path.home()
                / '.Ra_Reader'
            )

        self.config_file = (
            self.config_dir
            / 'settings.json'
        )

        self.icons_dir = (
            self.base_dir / '0'
        )

        self.books_dir = (
            self.base_dir / '1'
        )

        self.transmissions_dir = (
            self.base_dir / '2'
        )

        self.projects_dir = (
            self.base_dir / '3'
        )

        settings = (
            self.load_settings()
        )

        # =====================================================
        # Theme
        # =====================================================

        self.theme_name = (
            settings.get(
                'theme',
                'day'
            )
            if settings
            else 'day'
        )

        if (
            self.theme_name
            not in self.THEMES
        ):
            self.theme_name = 'day'

        # =====================================================
        # Fonts
        # =====================================================

        self.font_size = 15

        self.label_font = (
            'Alice',
            self.font_size
        )

        self.status_font = (
            'Alice',
            12
        )

        self.reader_font_size = 13

        # Настраиваемые параметры содержимого.
        self.content_font_family = 'Alice'

        self.reader_text_max_width = (
            self.READER_TEXT_MAX_WIDTH
        )

        self.content_full_justify = False

        self.video_folder = None
        self.audio_folder = None

        # Последний каталог ручного выбора media-файла
        # для Передач.
        self.last_media_file_directory = None

        # Индивидуальный marker для каждой темы.
        self.theme_marker_colors = {
            name: self.HIGHLIGHT_COLOR
            for name in self.THEMES
        }

        # Settings window / transaction.
        self.settings_window = None
        self.settings_canvas = None
        self.settings_snapshot = None
        self.settings_preview_active = False

        self.settings_theme_underline = None
        self.settings_color_items = {}
        self.settings_format_item = None

        # Help / About window.
        self.help_window = None
        self.help_canvas = None
        self.help_content = None
        self.help_canvas_window = None
        self.help_image_refs = []

        self.settings_font_combo = None
        self.settings_font_size_var = None
        self.settings_page_width_var = None

        # Existing reader behaviour remains default.
        self.reader_narrow_mode = True

        if settings:
            self.reader_font_size = (
                settings.get(
                    'reader_font_size',
                    13
                )
            )

            self.content_font_family = str(
                settings.get(
                    'content_font_family',
                    'Alice'
                )
                or 'Alice'
            )

            try:
                self.reader_text_max_width = max(
                    200,
                    int(
                        settings.get(
                            'reader_text_max_width',
                            self.READER_TEXT_MAX_WIDTH
                        )
                    )
                )
            except Exception:
                self.reader_text_max_width = (
                    self.READER_TEXT_MAX_WIDTH
                )

            self.content_full_justify = bool(
                settings.get(
                    'content_full_justify',
                    False
                )
            )

            self.video_folder = settings.get(
                'video_folder'
            )

            self.audio_folder = settings.get(
                'audio_folder'
            )

            last_media_directory = settings.get(
                'last_media_file_directory'
            )

            if last_media_directory:
                try:
                    self.last_media_file_directory = (
                        Path(
                            last_media_directory
                        )
                    )
                except Exception:
                    self.last_media_file_directory = None

            saved_markers = (
                settings.get(
                    'theme_marker_colors',
                    {}
                )
                or {}
            )

            for theme_key in self.THEMES:
                value = saved_markers.get(
                    theme_key
                )

                if (
                    isinstance(value, str)
                    and re.fullmatch(
                        r'#[0-9a-fA-F]{6}',
                        value
                    )
                ):
                    self.theme_marker_colors[
                        theme_key
                    ] = value

            saved_themes = (
                settings.get(
                    'theme_colors',
                    {}
                )
                or {}
            )

            for theme_key, values in saved_themes.items():
                if (
                    theme_key in self.THEMES
                    and isinstance(values, dict)
                ):
                    for color_key in (
                        'background',
                        'text'
                    ):
                        value = values.get(
                            color_key
                        )

                        if (
                            isinstance(value, str)
                            and re.fullmatch(
                                r'#[0-9a-fA-F]{6}',
                                value
                            )
                        ):
                            self.THEMES[
                                theme_key
                            ][
                                color_key
                            ] = value

            self.reader_narrow_mode = bool(
                settings.get(
                    'reader_narrow_mode',
                    True
                )
            )

        self.reader_font = (
            self.content_font_family,
            self.reader_font_size
        )

        self.reader_font_bold = (
            self.content_font_family,
            self.reader_font_size,
            'bold'
        )

        self.reader_font_italic = (
            self.content_font_family,
            self.reader_font_size,
            'italic'
        )

        # HTML figcaption ranges.
        self.document_italic_ranges = []

        # =====================================================
        # Persistent reader data
        # =====================================================

        self.reading_positions = {}
        self.bookmarks = {}
        self.highlights = {}

        self.last_opened_transmission = None
        self.last_opened_book = None
        self.last_opened_project = None
        self.last_opened_external = None

        self.external_files = []

        self.last_file_directory = None

        # =====================================================
        # Global-search settings
        # =====================================================

        self.global_search_groups = {
            'books': True,
            'transmissions': True,
            'projects': True,
            'files': True
        }

        # Documents excluded from global search.
        self.search_excluded_paths = set(
            str(value)
            for value
            in (
                (settings or {}).get(
                    'search_excluded_paths',
                    []
                )
                or []
            )
        )

        # Hit areas used by Books / Transmissions context menu.
        self.search_list_hit_items = []

        self.search_exclusion_menu = None

        # Factory reset suppresses accidental recreation of
        # settings.json until a new setting is explicitly saved.
        self.factory_reset_pending = False

        # =====================================================
        # Notes persistent data
        # =====================================================

        # True = заметки имеют reader-like max width.
        # При отсутствии сохранённой настройки этот режим
        # включён по умолчанию.
        self.notes_narrow_mode = True

        # [
        #   {
        #       "id": 1,
        #       "name": "Лист 1",
        #       "text": "...",
        #       "bold": [[0, 10]],
        #       "highlights": [[20, 30]]
        #   }
        # ]
        self.notes_sheets = []

        self.notes_current_sheet_id = None
        self.notes_next_sheet_id = 1

        # =====================================================
        # Load persistent settings
        # =====================================================

        if settings:
            self.reading_positions = (
                settings.get(
                    'reading_positions',
                    {}
                )
                or {}
            )

            self.bookmarks = (
                settings.get(
                    'bookmarks',
                    {}
                )
                or {}
            )

            self.highlights = (
                settings.get(
                    'highlights',
                    {}
                )
                or {}
            )

            last_transmission = (
                settings.get(
                    'last_opened_transmission'
                )
            )

            # Совместимость со старой версией.
            if not last_transmission:
                last_transmission = (
                    settings.get(
                        'last_opened_file'
                    )
                )

            last_book = (
                settings.get(
                    'last_opened_book'
                )
            )

            last_project = (
                settings.get(
                    'last_opened_project'
                )
            )

            last_external = (
                settings.get(
                    'last_opened_external'
                )
            )

            if last_transmission:
                self.last_opened_transmission = (
                    Path(
                        last_transmission
                    )
                )

            if last_book:
                self.last_opened_book = (
                    Path(
                        last_book
                    )
                )

            if last_project:
                self.last_opened_project = (
                    Path(
                        last_project
                    )
                )

            if last_external:
                self.last_opened_external = (
                    Path(
                        last_external
                    )
                )

            saved_external_files = (
                settings.get(
                    'external_files',
                    []
                )
                or []
            )

            for value in saved_external_files:
                try:
                    path = (
                        Path(value)
                    )

                    if str(path) not in {
                        str(item)
                        for item
                        in self.external_files
                    }:
                        self.external_files.append(
                            path
                        )

                except Exception:
                    pass

            last_directory = (
                settings.get(
                    'last_file_directory'
                )
            )

            if last_directory:
                try:
                    self.last_file_directory = (
                        Path(
                            last_directory
                        )
                    )

                except Exception:
                    self.last_file_directory = (
                        None
                    )

            saved_groups = (
                settings.get(
                    'global_search_groups',
                    {}
                )
                or {}
            )

            for group in (
                'books',
                'transmissions',
                'projects',
                'files'
            ):
                if group in saved_groups:
                    self.global_search_groups[
                        group
                    ] = bool(
                        saved_groups[
                            group
                        ]
                    )

            self.notes_narrow_mode = bool(
                settings.get(
                    'notes_narrow_mode',
                    True
                )
            )

            saved_notes = (
                settings.get(
                    'notes_sheets',
                    []
                )
                or []
            )

            self.notes_sheets = (
                self.normalize_notes_sheets(
                    saved_notes
                )
            )

            saved_current_sheet = (
                settings.get(
                    'notes_current_sheet_id'
                )
            )

            try:
                self.notes_current_sheet_id = (
                    int(
                        saved_current_sheet
                    )
                )

            except Exception:
                self.notes_current_sheet_id = (
                    None
                )

            try:
                self.notes_next_sheet_id = max(
                    1,
                    int(
                        settings.get(
                            'notes_next_sheet_id',
                            1
                        )
                    )
                )

            except Exception:
                self.notes_next_sheet_id = 1

        self.normalize_saved_bookmarks()
        self.normalize_saved_highlights()

        # Если заметок ещё нет — создаём первый лист.
        if not self.notes_sheets:
            self.notes_sheets = [
                {
                    'id': 1,
                    'name': 'Лист 1',
                    'text': '',
                    'bold': [],
                    'highlights': []
                }
            ]

            self.notes_current_sheet_id = 1
            self.notes_next_sheet_id = 2

        existing_note_ids = {
            sheet['id']
            for sheet
            in self.notes_sheets
        }

        if (
            self.notes_current_sheet_id
            not in existing_note_ids
        ):
            self.notes_current_sheet_id = (
                self.notes_sheets[
                    0
                ][
                    'id'
                ]
            )

        if existing_note_ids:
            self.notes_next_sheet_id = max(
                self.notes_next_sheet_id,
                max(
                    existing_note_ids
                ) + 1
            )

        # =====================================================
        # Window settings
        # =====================================================

        self.window_geometry = (
            settings or {}
        ).get(
            'geometry',
            '1200x800'
        )

        self.window_position = (
            settings or {}
        ).get(
            'position',
            '+100+100'
        )

        # =====================================================
        # Images
        # =====================================================

        self.images = {}
        self.photo_frames = {}

        self.load_images()

        # =====================================================
        # Fade
        # =====================================================

        self.text_fade_colors = []
        self.text_fade_colors_semi = []

        self.rebuild_fade_colors()

        # =====================================================
        # General UI
        # =====================================================

        self.current_screen = 'home'

        self.screen_elements = []
        self.highlight_items = []
        self.hover_areas = []

        self.current_hover = None
        self.is_transitioning = False

        self.canvas = None
        self.text_widget = None
        self.reader_container = None

        self.main_frame = None
        self.middle_frame = None

        self.top_canvas = None
        self.bottom_canvas = None

        self.scrollbar = None

        self.resize_timer = None

        self.last_size = (
            0,
            0
        )

        self.last_overlay_width = 0

        # =====================================================
        # Reader
        # =====================================================

        self.reader_content = ''

        self.reader_lines_per_page = 1

        self.reader_page_start = 0
        self.reader_page_end = 0

        self.reader_current_lines = []

        self.reader_back_history = []
        self.reader_forward_history = []

        self.reader_page_cache = {}

        self.reader_display_map = []

        self.reader_normal_tkfont = None
        self.reader_bold_tkfont = None

        self.measure_cache_normal = {}
        self.measure_cache_bold = {}

        self.reader_source_type = None

        # Reader width toggle.
        self.reader_width_button = None
        self.reader_width_button_bg = None

        self.document_bold_ranges = []

        self.document_images = []
        self.document_image_positions = []

        self.reader_page_photo_images = []

        # Two-page reader.
        self.reader_two_page_mode = False
        self.second_text_widget = None
        self.reader_second_page = None
        self.reader_second_display_map = []
        self.reader_second_page_photo_images = []
        self.reader_columns_frame = None

        # =====================================================
        # Project formatting
        # =====================================================

        self.reader_is_imam_dialogue = False

        self.reader_title_range = None

        # =====================================================
        # Timecodes
        # =====================================================

        self.timecodes = []
        self.timecode_positions = []

        self.current_timecode = (
            '00:00:00'
        )

        # =====================================================
        # Lists
        # =====================================================

        self.transmissions_list = []
        self.books_list = []

        self.selected_file = None
        self.selected_source_type = None

        self.save_timer = None

        # =====================================================
        # Slider
        # =====================================================

        self.is_dragging_runner = False

        self.bookmark_marker_items = []
        self.bookmark_marker_images = []

        self.search_marker_items = []

        # =====================================================
        # Overlay
        # =====================================================

        self.overlay_buttons = []
        self.overlay_hover = None

        self.bottom_tc_item = None
        self.bottom_pct_item = None

        self.runner_item = None
        self.line_item = None

        self.theme_underline_item = None

        self.continue_item = None
        self.continue_hover = False

        # =====================================================
        # List states
        # =====================================================

        self.transmissions_yview = 0.0
        self.restore_transmissions_view = False

        self.books_yview = 0.0
        self.restore_books_view = False

        self.files_yview = 0.0
        self.restore_files_view = False

        # =====================================================
        # Context menus
        # =====================================================

        self.context_menu = None

        self.bookmark_icon_menu = None
        self.bookmark_marker_menu = None
        self.fill_icon_menu = None

        self.context_bookmark_position = None

        self.external_file_menu = None
        self.context_external_file = None

        # =====================================================
        # Reader search
        # =====================================================

        self.search_active = False

        self.search_entry = None
        self.search_box_item = None
        self.search_count_item = None

        self.search_context_menu = None

        self.search_matches = []
        self.search_current_index = -1
        self.search_query = ''

        self.search_layout = 'wide'

        self.search_hide_secondary = False
        self.search_hide_primary = False

        # =====================================================
        # Projects
        # =====================================================

        self.project_hit_items = []
        self.project_hover_index = None

        # =====================================================
        # Files
        # =====================================================

        self.file_hit_items = []

        # =====================================================
        # RAM document cache
        # =====================================================

        self.document_cache = {}

        self.document_cache_ready = False

        # -----------------------------------------------------
        # Parsed Reader cache.
        #
        # document_cache выше предназначен прежде всего
        # для поиска. Здесь хранится уже разобранный документ
        # Reader, чтобы HTML/MHTML не парсился при каждом
        # повторном открытии.
        # -----------------------------------------------------

        self.reader_document_cache = {}

        # Точное состояние страницы с изображениями.
        self.reader_image_cursor = 0
        self.reader_page_image_cursor_start = 0
        self.reader_page_image_cursor_end = 0

        # История теперь может хранить tuple:
        # (text_position, image_cursor)
        self.reader_back_history = []
        self.reader_forward_history = []

        # Loading indicator.
        self.reader_loading_frame = None
        self.reader_loading_canvas = None
        self.reader_loading_text_item = None
        self.reader_loading_bar_item = None

        # =====================================================
        # Global search UI
        # =====================================================

        self.global_search_entry = None

        self.global_search_box_item = None
        self.global_search_count_item = None

        self.global_search_query = ''

        self.global_search_results = []

        self.global_search_page = 0

        self.global_search_result_items = []

        self.global_search_hover_index = (
            None
        )

        self.global_search_checkbox_items = []

        self.global_search_canvas = None
        self.global_search_scrollbar = None

        self.global_search_content_frame = None
        self.global_search_window_item = None

        self.global_search_saved_yview = 0.0

        # Глобальный поиск запускается через 2 секунды
        # после последнего изменения поискового запроса.
        self.global_search_debounce_timer = None
        self.global_search_debounce_delay = 2000

        # =====================================================
        # Global search -> reader
        # =====================================================

        self.reader_from_global_search = False

        self.global_search_target_position = (
            None
        )

        self.global_search_return_page = 0
        self.global_search_return_yview = 0.0

        self.suppress_reader_position_save = False

        # =====================================================
        # Notes runtime
        # =====================================================

        self.notes_container = None

        self.notes_text = None
        self.notes_scrollbar = None

        self.notes_bottom_canvas = None

        self.notes_bold_button = None
        self.notes_fill_button = None
        self.notes_add_button = None

        self.notes_width_button = None
        self.notes_width_button_bg = None

        self.notes_tab_items = []

        self.notes_context_menu = None
        self.notes_format_menu = None
        self.notes_fill_menu = None

        self.notes_save_timer = None

        self.notes_loading = False

        # Drag tabs.
        self.notes_drag_sheet_id = None
        self.notes_drag_start_x = None
        self.notes_drag_active = False
        self.notes_drag_indicator = None

        # Excel-like live tab dragging.
        self.notes_drag_ghost_rect = None
        self.notes_drag_ghost_text = None

        self.notes_drag_origin_index = None
        self.notes_drag_drop_index = None

        self.notes_drag_tab_width = 0
        self.notes_drag_tab_y = 0

        self.notes_drag_valid_zone = None

        self.notes_tab_animation_id = None

        # =====================================================
        # Notes search
        # =====================================================

        self.notes_search_active = False
        self.notes_search_entry = None
        self.notes_search_count_item = None

        self.notes_search_query = ''
        self.notes_search_matches = []
        self.notes_search_current_index = -1

        self.notes_tabs_layout_timer = None

        # =====================================================

        self.setup_window()
        self.create_ui()

        self.root.protocol(
            'WM_DELETE_WINDOW',
            self.on_closing
        )

        self.root.bind(
            '<Configure>',
            self.on_configure
        )

        self.root.bind(
            '<Escape>',
            self.on_escape
        )

        self.root.bind_all(
            '<MouseWheel>',
            self.on_global_search_root_mousewheel,
            add='+'
        )

        self.root.bind_all(
            '<Button-4>',
            self.on_global_search_root_mousewheel,
            add='+'
        )

        self.root.bind_all(
            '<Button-5>',
            self.on_global_search_root_mousewheel,
            add='+'
        )

        self.root.bind_all(
            '<Prior>',
            self.on_global_search_page_key,
            add='+'
        )

        self.root.bind_all(
            '<Next>',
            self.on_global_search_page_key,
            add='+'
        )

        # Все документы заранее загружаются
        # в оперативную память.
        self.root.after(
            1,
            self.rebuild_document_cache
        )

    # =========================================================
    # THEME
    # =========================================================

    def theme(self):
        return self.THEMES[
            self.theme_name
        ]

    def bg_color(self):
        return self.theme()[
            'background'
        ]

    def text_color(self):
        return self.theme()[
            'text'
        ]

    def secondary_color(self):
        return self.theme()[
            'secondary'
        ]

    def line_color(self):
        return self.theme()[
            'line'
        ]

    def hex_to_rgb(
        self,
        color
    ):
        color = (
            color.lstrip(
                '#'
            )
        )

        return (
            int(
                color[0:2],
                16
            ),
            int(
                color[2:4],
                16
            ),
            int(
                color[4:6],
                16
            )
        )

    def rgb_to_hex(
        self,
        rgb
    ):
        return (
            '#'
            + ''.join(
                f'{max(0, min(255, int(v))):02x}'
                for v in rgb
            )
        )

    def blend_colors(
        self,
        foreground,
        background,
        alpha
    ):
        fr, fg, fb = (
            self.hex_to_rgb(
                foreground
            )
        )

        br, bg, bb = (
            self.hex_to_rgb(
                background
            )
        )

        return self.rgb_to_hex((
            br + (
                fr - br
            ) * alpha,

            bg + (
                fg - bg
            ) * alpha,

            bb + (
                fb - bb
            ) * alpha
        ))

    def get_reader_highlight_color(self):
        color = self.theme_marker_colors.get(
            self.theme_name,
            self.HIGHLIGHT_COLOR
        )

        if self.theme_name == 'night':
            return self.blend_colors(
                color,
                self.bg_color(),
                0.30
            )

        return color

    def get_search_normal_display_color(self):
        return self.blend_colors(
            self.SEARCH_NORMAL_COLOR,
            self.bg_color(),
            0.50
        )

    def get_search_current_display_color(self):
        return (
            self.SEARCH_CURRENT_COLOR
        )

    def rebuild_fade_colors(self):
        self.text_fade_colors = []
        self.text_fade_colors_semi = []

        bg = self.bg_color()
        fg = self.text_color()

        secondary = (
            self.secondary_color()
        )

        for i in range(11):
            alpha = (
                i / 10.0
            )

            self.text_fade_colors.append(
                self.blend_colors(
                    fg,
                    bg,
                    alpha
                )
            )

            self.text_fade_colors_semi.append(
                self.blend_colors(
                    secondary,
                    bg,
                    alpha
                )
            )

    def set_theme(
        self,
        theme_name
    ):
        if (
            theme_name
            not in self.THEMES
        ):
            return

        if (
            theme_name
            == self.theme_name
        ):
            return

        self.theme_name = (
            theme_name
        )

        self.rebuild_fade_colors()

        self.apply_theme_to_widgets()

        if (
            self.current_screen
            == 'reader'
        ):
            if self.text_widget:
                self.render_reader_page({
                    'start':
                        self.reader_page_start,

                    'end':
                        self.reader_page_end,

                    'lines':
                        self.reader_current_lines
                })

            self.build_overlay()

        elif (
            self.current_screen
            == 'search'
        ):
            self.draw_global_search_screen(
                preserve_scroll=True
            )

            self.build_overlay()

        elif (
            self.current_screen
            == 'notes'
        ):
            self.save_current_note_sheet()

            self.draw_notes_screen()

            self.build_overlay()

        else:
            self.draw_current_screen(
                10
            )

        self.save_settings()

    def apply_theme_to_widgets(self):
        bg = (
            self.bg_color()
        )

        try:
            self.root.configure(
                bg=bg
            )

        except Exception:
            pass

        for widget in (
            self.main_frame,
            self.middle_frame,
            self.reader_container,
            self.canvas,
            self.top_canvas,
            self.bottom_canvas,
            self.global_search_canvas,
            self.global_search_content_frame,
            self.notes_container,
            self.notes_bottom_canvas
        ):
            if widget:
                try:
                    widget.configure(
                        bg=bg
                    )

                except Exception:
                    pass

        if self.text_widget:
            try:
                self.text_widget.configure(
                    bg=bg,
                    fg=self.text_color(),
                    insertbackground=(
                        self.text_color()
                    )
                )

            except Exception:
                pass

        if self.notes_text:
            try:
                self.notes_text.configure(
                    bg=bg,
                    fg=self.text_color(),
                    insertbackground=(
                        self.text_color()
                    ),
                    selectforeground=(
                        self.text_color()
                    )
                )

                self.configure_notes_tags()

            except Exception:
                pass

        for entry in (
            self.search_entry,
            self.global_search_entry
        ):
            if entry:
                try:
                    entry.configure(
                        bg=bg,
                        fg=self.text_color(),
                        insertbackground=(
                            self.text_color()
                        )
                    )

                except Exception:
                    pass

    # =========================================================
    # RANGES / NORMALIZATION
    # =========================================================

    def merge_ranges(
        self,
        ranges
    ):
        cleaned = []

        for item in ranges:
            try:
                start = int(
                    item[0]
                )

                end = int(
                    item[1]
                )

            except Exception:
                continue

            if end > start:
                cleaned.append(
                    [
                        start,
                        end
                    ]
                )

        if not cleaned:
            return []

        cleaned.sort(
            key=lambda item: (
                item[0],
                item[1]
            )
        )

        merged = [
            cleaned[0][:]
        ]

        for start, end in (
            cleaned[1:]
        ):
            previous = (
                merged[-1]
            )

            if (
                start
                <= previous[1]
            ):
                previous[1] = max(
                    previous[1],
                    end
                )

            else:
                merged.append(
                    [
                        start,
                        end
                    ]
                )

        return merged

    def normalize_saved_bookmarks(self):
        normalized = {}

        for key, value in (
            self.bookmarks.items()
        ):
            values = (
                value
                if isinstance(
                    value,
                    list
                )
                else [
                    value
                ]
            )

            result = []

            for item in values:
                try:
                    if (
                        isinstance(
                            item,
                            str
                        )
                        and '.' in item
                    ):
                        continue

                    position = int(
                        item
                    )

                except Exception:
                    continue

                if position >= 0:
                    result.append(
                        position
                    )

            normalized[key] = (
                sorted(
                    set(
                        result
                    )
                )
            )

        self.bookmarks = (
            normalized
        )

    def normalize_saved_highlights(self):
        normalized = {}

        for key, value in (
            self.highlights.items()
        ):
            if not isinstance(
                value,
                list
            ):
                continue

            ranges = []

            for item in value:
                if (
                    not isinstance(
                        item,
                        (
                            list,
                            tuple
                        )
                    )
                    or len(
                        item
                    ) != 2
                ):
                    continue

                try:
                    start = int(
                        item[0]
                    )

                    end = int(
                        item[1]
                    )

                except Exception:
                    continue

                if (
                    end > start
                    and start >= 0
                ):
                    ranges.append(
                        [
                            start,
                            end
                        ]
                    )

            normalized[key] = (
                self.merge_ranges(
                    ranges
                )
            )

        self.highlights = (
            normalized
        )

    # =========================================================
    # NOTES NORMALIZATION
    # =========================================================

    def normalize_notes_sheets(
        self,
        sheets
    ):
        result = []

        used_ids = set()

        for item in sheets:
            if not isinstance(
                item,
                dict
            ):
                continue

            try:
                sheet_id = int(
                    item.get(
                        'id'
                    )
                )

            except Exception:
                continue

            if (
                sheet_id <= 0
                or sheet_id in used_ids
            ):
                continue

            used_ids.add(
                sheet_id
            )

            name = str(
                item.get(
                    'name',
                    f'Лист {sheet_id}'
                )
            ).strip()

            if not name:
                name = (
                    f'Лист {sheet_id}'
                )

            text = str(
                item.get(
                    'text',
                    ''
                )
            )

            text_length = len(
                text
            )

            bold = (
                self.normalize_note_ranges(
                    item.get(
                        'bold',
                        []
                    ),
                    text_length
                )
            )

            highlights = (
                self.normalize_note_ranges(
                    item.get(
                        'highlights',
                        []
                    ),
                    text_length
                )
            )

            result.append({
                'id':
                    sheet_id,

                'name':
                    name,

                'text':
                    text,

                'bold':
                    bold,

                'highlights':
                    highlights
            })

            if (
                len(result)
                >= self.NOTES_MAX_SHEETS
            ):
                break

        return result

    def normalize_note_ranges(
        self,
        ranges,
        text_length
    ):
        result = []

        if not isinstance(
            ranges,
            list
        ):
            return result

        for item in ranges:
            if (
                not isinstance(
                    item,
                    (
                        list,
                        tuple
                    )
                )
                or len(item) != 2
            ):
                continue

            try:
                start = int(
                    item[0]
                )

                end = int(
                    item[1]
                )

            except Exception:
                continue

            start = max(
                0,
                min(
                    start,
                    text_length
                )
            )

            end = max(
                0,
                min(
                    end,
                    text_length
                )
            )

            if end > start:
                result.append(
                    [
                        start,
                        end
                    ]
                )

        return (
            self.merge_ranges(
                result
            )
        )

    # =========================================================
    # IMAGES
    # =========================================================

    def load_images(self):
        placeholders = {
            '01': (
                188,
                188,
                '01'
            ),

            '02': (
                188,
                188,
                '02'
            ),

            '03': (
                188,
                188,
                '03'
            ),

            '04': (
                234,
                272,
                '04'
            ),

            # Reading menu:
            # strictly 24x24.
            '05': (
                24,
                24,
                '05'
            ),

            '06': (
                24,
                24,
                '06'
            ),

            '07': (
                24,
                24,
                '07'
            ),

            '08': (
                320,
                72,
                '08'
            ),

            '09': (
                800,
                36,
                '09'
            ),

            '10': (
                24,
                24,
                '10'
            ),

            '11': (
                24,
                24,
                '11'
            ),

            '12': (
                24,
                24,
                '12'
            ),

            '13': (
                24,
                24,
                '13'
            ),

            '14': (
                24,
                24,
                '14'
            ),

            '15': (
                34,
                34,
                '15'
            ),

            '16': (
                24,
                24,
                '16'
            ),

            '17': (
                24,
                24,
                '17'
            ),

            '18': (
                24,
                24,
                '18'
            ),

            '19': (
                24,
                24,
                '19'
            ),

            '20': (
                24,
                24,
                '20'
            ),

            '21': (
                24,
                24,
                '21'
            ),

            '22': (
                24,
                24,
                '22'
            ),

            '23': (
                24,
                24,
                '23'
            ),

            '24': (
                214,
                30,
                '24'
            ),

            '25': (
                214,
                30,
                '25'
            ),

            '26': (
                24,
                2,
                '26'
            ),

            '27': (
                24,
                24,
                '27'
            ),

            '28': (
                24,
                24,
                '28'
            ),

            '29': (
                24,
                24,
                '29'
            ),

            '30': (
                476,
                30,
                '30'
            ),

            '31': (
                24,
                24,
                '31'
            ),

            '32': (
                24,
                24,
                '32'
            ),

            '33': (
                24,
                24,
                '33'
            ),

            '34': (
                146,
                30,
                '34'
            ),

            '36': (
                24,
                24,
                '36'
            ),

            '37': (
                24,
                24,
                '37'
            ),

            '38': (
                24,
                24,
                '38'
            ),

            '39': (
                24,
                24,
                '39'
            ),

            # Notes bold.
            '40': (
                24,
                24,
                '40'
            ),

            # Notes width toggle.
            '41': (
                24,
                24,
                '41'
            ),

            '42': (
                24,
                24,
                '42'
            ),

            '43': (
                24,
                24,
                '43'
            ),

            '44': (
                24,
                24,
                '44'
            ),

            '45': (
                24,
                24,
                '45'
            ),

            '46': (
                24,
                24,
                '46'
            ),
        }

        icon_24 = {
            '05',
            '06',
            '07',

            '10',
            '11',
            '12',
            '13',
            '14',

            '16',
            '17',
            '18',
            '19',
            '20',
            '21',
            '22',
            '23',

            '27',
            '28',
            '29',

            '31',
            '32',
            '33',

            '36',
            '37',
            '38',
            '39',
            '40',
            '41',
            '42',
            '43',
            '44',
            '45',
            '46'
        }

        for key, (
            width,
            height,
            text
        ) in placeholders.items():

            path = (
                self.icons_dir
                / f'{key}.png'
            )

            try:
                if path.exists():
                    image = (
                        Image.open(
                            path
                        ).convert(
                            'RGBA'
                        )
                    )

                    target = None

                    if key in icon_24:
                        target = (
                            24,
                            24
                        )

                    elif key == '15':
                        target = (
                            34,
                            34
                        )

                    elif key in (
                        '24',
                        '25'
                    ):
                        target = (
                            214,
                            30
                        )

                    elif key == '26':
                        target = (
                            24,
                            2
                        )

                    elif key == '30':
                        target = (
                            476,
                            30
                        )

                    elif key == '34':
                        target = (
                            146,
                            30
                        )

                    if (
                        target
                        and image.size
                        != target
                    ):
                        image = image.resize(
                            target,
                            Image.LANCZOS
                        )

                    self.images[
                        key
                    ] = image

                else:
                    self.images[
                        key
                    ] = (
                        self.create_placeholder(
                            width,
                            height,
                            text
                        )
                    )

            except Exception:
                self.images[
                    key
                ] = (
                    self.create_placeholder(
                        width,
                        height,
                        text
                    )
                )

        for key, image in (
            self.images.items()
        ):
            frames = []

            for i in range(11):
                ratio = (
                    i / 10.0
                )

                frame = (
                    image.copy()
                )

                alpha = (
                    frame
                    .split()[3]
                    .point(
                        lambda value,
                        r=ratio:
                        int(
                            value * r
                        )
                    )
                )

                frame.putalpha(
                    alpha
                )

                frames.append(
                    ImageTk.PhotoImage(
                        frame
                    )
                )

            self.photo_frames[
                key
            ] = frames

    def create_placeholder(
        self,
        width,
        height,
        text
    ):
        if height <= 3:
            return Image.new(
                'RGBA',
                (
                    width,
                    height
                ),
                (
                    80,
                    80,
                    80,
                    255
                )
            )

        image = Image.new(
            'RGBA',
            (
                width,
                height
            ),
            (
                220,
                220,
                220,
                255
            )
        )

        draw = (
            ImageDraw.Draw(
                image
            )
        )

        draw.rectangle(
            (
                1,
                1,
                width - 2,
                height - 2
            ),
            outline=(
                150,
                150,
                150,
                255
            ),
            width=2
        )

        try:
            font = (
                ImageFont.truetype(
                    'arial.ttf',
                    max(
                        9,
                        int(
                            height * 0.4
                        )
                    )
                )
            )

        except Exception:
            font = (
                ImageFont.load_default()
            )

        bbox = (
            draw.textbbox(
                (
                    0,
                    0
                ),
                text,
                font=font
            )
        )

        tw = (
            bbox[2]
            - bbox[0]
        )

        th = (
            bbox[3]
            - bbox[1]
        )

        draw.text(
            (
                (
                    width - tw
                ) // 2,

                (
                    height - th
                ) // 2 - 2
            ),
            text,
            fill=(
                120,
                120,
                120,
                255
            ),
            font=font
        )

        return image

    # =========================================================
    # SETTINGS
    # =========================================================

    def setup_window(self):
        settings = (
            self.load_settings()
        )

        if (
            settings
            and not settings.get(
                'first_run',
                True
            )
        ):
            geometry = (
                settings.get(
                    'geometry',
                    '1200x800'
                )
            )

            position = (
                settings.get(
                    'position',
                    '+100+100'
                )
            )

            state = (
                settings.get(
                    'state',
                    'normal'
                )
            )

            self.root.geometry(
                f'{geometry}{position}'
            )

            self.root.update_idletasks()

            if state == 'zoomed':
                self.root.state(
                    'zoomed'
                )

        else:
            self.root.state(
                'zoomed'
            )

    def load_settings(self):
        try:
            if (
                self.config_file.exists()
            ):
                with open(
                    self.config_file,
                    'r',
                    encoding='utf-8'
                ) as file:
                    return json.load(
                        file
                    )

        except Exception as error:
            print(
                'Ошибка загрузки настроек:',
                error
            )

        return None

    def serialize_notes_sheets(self):
        result = []

        for sheet in (
            self.notes_sheets
        ):
            result.append({
                'id':
                    int(
                        sheet['id']
                    ),

                'name':
                    str(
                        sheet['name']
                    ),

                'text':
                    str(
                        sheet.get(
                            'text',
                            ''
                        )
                    ),

                'bold':
                    [
                        [
                            int(a),
                            int(b)
                        ]
                        for a, b
                        in sheet.get(
                            'bold',
                            []
                        )
                    ],

                'highlights':
                    [
                        [
                            int(a),
                            int(b)
                        ]
                        for a, b
                        in sheet.get(
                            'highlights',
                            []
                        )
                    ]
            })

        return result

    def save_settings(self):
        if self.settings_preview_active:
            return

        if getattr(
            self,
            'factory_reset_pending',
            False
        ):
            return

        try:
            self.config_dir.mkdir(
                parents=True,
                exist_ok=True
            )

            try:
                state = (
                    self.root.state()
                )

            except Exception:
                state = 'normal'

            settings = {
                'first_run':
                    False,

                'geometry':
                    self.window_geometry,

                'position':
                    self.window_position,

                'state':
                    state,

                'reader_font_size':
                    self.reader_font_size,

                'reader_narrow_mode':
                    bool(
                        self.reader_narrow_mode
                    ),

                'content_font_family':
                    self.content_font_family,

                'reader_text_max_width':
                    int(
                        self.reader_text_max_width
                    ),

                'content_full_justify':
                    bool(
                        self.content_full_justify
                    ),

                'video_folder':
                    self.video_folder,

                'audio_folder':
                    self.audio_folder,

                'last_media_file_directory':
                    (
                        str(
                            self.last_media_file_directory
                        )
                        if self.last_media_file_directory
                        else None
                    ),

                'theme_marker_colors':
                    dict(
                        self.theme_marker_colors
                    ),

                'theme_colors':
                    {
                        key: {
                            'background':
                                value['background'],

                            'text':
                                value['text']
                        }
                        for key, value
                        in self.THEMES.items()
                    },

                'reading_positions':
                    self.reading_positions,

                'bookmarks':
                    self.bookmarks,

                'highlights':
                    self.highlights,

                'theme':
                    self.theme_name,

                'last_opened_transmission':
                    (
                        str(
                            self.last_opened_transmission
                        )
                        if
                        self.last_opened_transmission
                        else None
                    ),

                'last_opened_book':
                    (
                        str(
                            self.last_opened_book
                        )
                        if
                        self.last_opened_book
                        else None
                    ),

                'last_opened_project':
                    (
                        str(
                            self.last_opened_project
                        )
                        if
                        self.last_opened_project
                        else None
                    ),

                'last_opened_external':
                    (
                        str(
                            self.last_opened_external
                        )
                        if
                        self.last_opened_external
                        else None
                    ),

                'external_files':
                    [
                        str(
                            path
                        )
                        for path
                        in self.external_files
                    ],

                'last_file_directory':
                    (
                        str(
                            self.last_file_directory
                        )
                        if
                        self.last_file_directory
                        else None
                    ),

                'global_search_groups':
                    dict(
                        self.global_search_groups
                    ),

                'search_excluded_paths':
                    sorted(
                        self.search_excluded_paths
                    ),

                'notes_narrow_mode':
                    bool(
                        self.notes_narrow_mode
                    ),

                'notes_sheets':
                    self.serialize_notes_sheets(),

                'notes_current_sheet_id':
                    self.notes_current_sheet_id,

                'notes_next_sheet_id':
                    self.notes_next_sheet_id
            }

            with open(
                self.config_file,
                'w',
                encoding='utf-8'
            ) as file:
                json.dump(
                    settings,
                    file,
                    ensure_ascii=False,
                    indent=4
                )

        except Exception as error:
            print(
                'Ошибка сохранения настроек:',
                error
            )

    # =========================================================
    # WINDOW TITLE / PROJECT NAMES
    # =========================================================

    def is_imam_project_file(
        self,
        path
    ):
        if not path:
            return False

        return bool(
            re.fullmatch(
                (
                    r'Беседы с Имамом '
                    r'[1-6]\.fb2'
                ),
                Path(
                    path
                ).name,
                flags=re.IGNORECASE
            )
        )

    def is_alone_project_file(
        self,
        path
    ):
        if not path:
            return False

        path = (
            Path(
                path
            )
        )

        try:
            same_parent = (
                path.resolve().parent
                == self.projects_dir.resolve()
            )

        except Exception:
            same_parent = (
                path.parent
                == self.projects_dir
            )

        if not same_parent:
            return False

        match = re.fullmatch(
            (
                r'(\d{2})'
                r'\.(?:fb2|md)'
            ),
            path.name,
            flags=re.IGNORECASE
        )

        if not match:
            return False

        return (
            1
            <= int(
                match.group(1)
            )
            <= 32
        )

    def get_alone_project_number(
        self,
        path
    ):
        if not self.is_alone_project_file(
            path
        ):
            return None

        match = re.match(
            r'^(\d{2})\.',
            Path(
                path
            ).name
        )

        if not match:
            return None

        return int(
            match.group(1)
        )

    def get_imam_project_number(
        self,
        path
    ):
        if not path:
            return None

        match = re.fullmatch(
            (
                r'Беседы с Имамом '
                r'([1-6])\.fb2'
            ),
            Path(
                path
            ).name,
            flags=re.IGNORECASE
        )

        if not match:
            return None

        return int(
            match.group(1)
        )

    def is_single_markdown_project(
        self,
        path
    ):
        if not path:
            return False

        return (
            Path(
                path
            ).name
            in {
                'Единое Зерно.md',
                'Фильм-расследование.md',
                'Исконная физика.md'
            }
        )

    def get_project_reader_title(
        self,
        path
    ):
        if not path:
            return None

        path = (
            Path(
                path
            )
        )

        alone_number = (
            self.get_alone_project_number(
                path
            )
        )

        if (
            alone_number
            is not None
        ):
            return (
                'Вдвоём наедине. '
                f'Выпуск {alone_number}'
            )

        imam_number = (
            self.get_imam_project_number(
                path
            )
        )

        if (
            imam_number
            is not None
        ):
            return (
                'Беседы с Имамом. '
                f'Часть {imam_number}'
            )

        return path.stem

    def get_project_search_title_lines(
        self,
        path
    ):
        path = (
            Path(
                path
            )
        )

        alone_number = (
            self.get_alone_project_number(
                path
            )
        )

        if (
            alone_number
            is not None
        ):
            return [
                'Вдвоём наедине',
                f'Выпуск {alone_number}'
            ]

        imam_number = (
            self.get_imam_project_number(
                path
            )
        )

        if (
            imam_number
            is not None
        ):
            return [
                'Беседы с Имамом',
                f'Часть {imam_number}'
            ]

        return [
            path.stem
        ]

    def get_reader_title_from_file(
        self,
        path
    ):
        if not path:
            return self.APP_TITLE

        if (
            self.reader_source_type
            == 'project'
        ):
            title = (
                self.get_project_reader_title(
                    path
                )
            )

            if title:
                return title

        stem = (
            Path(
                path
            ).stem.strip()
        )

        match = re.match(
            (
                r'^\d{4}-\d{2}-\d{2}'
                r'\s*-\s*(.+)$'
            ),
            stem
        )

        if match:
            return (
                match.group(1).strip()
            )

        match = re.match(
            (
                r'^(.*?)'
                r'\s*-\s*'
                r'\d{4}$'
            ),
            stem
        )

        if match:
            title = (
                match.group(1).strip()
            )

            if title:
                return title

        return stem

    def update_window_title(self):
        if (
            self.current_screen
            == 'reader'
            and self.selected_file
        ):
            self.root.title(
                self.get_reader_title_from_file(
                    self.selected_file
                )
            )

        else:
            self.root.title(
                self.APP_TITLE
            )

    # =========================================================
    # UI
    # =========================================================

    def create_ui(self):
        bg = (
            self.bg_color()
        )

        self.root.configure(
            bg=bg
        )

        self.main_frame = Frame(
            self.root,
            bg=bg
        )

        self.main_frame.pack(
            fill=tk.BOTH,
            expand=True
        )

        self.top_canvas = Canvas(
            self.main_frame,
            bg=bg,
            height=self.TOP_BAR_HEIGHT,
            highlightthickness=0
        )

        self.top_canvas.pack(
            side=tk.TOP,
            fill=tk.X
        )

        self.bottom_canvas = Canvas(
            self.main_frame,
            bg=bg,
            height=self.BOTTOM_BAR_HEIGHT,
            highlightthickness=0
        )

        self.bottom_canvas.pack(
            side=tk.BOTTOM,
            fill=tk.X
        )

        self.middle_frame = Frame(
            self.main_frame,
            bg=bg
        )

        self.middle_frame.pack(
            side=tk.TOP,
            fill=tk.BOTH,
            expand=True
        )

        self.canvas = Canvas(
            self.middle_frame,
            bg=bg,
            highlightthickness=0
        )

        self.canvas.pack(
            side=tk.LEFT,
            fill=tk.BOTH,
            expand=True
        )

        self.scrollbar = Scrollbar(
            self.middle_frame,
            orient=tk.VERTICAL,
            command=self.canvas.yview
        )

        self.canvas.configure(
            yscrollcommand=(
                self.scrollbar.set
            )
        )

        self.restore_normal_canvas_bindings()

        self.top_canvas.bind(
            '<Motion>',
            self.on_overlay_motion
        )

        self.top_canvas.bind(
            '<Leave>',
            self.on_overlay_leave
        )

        self.top_canvas.bind(
            '<Button-1>',
            self.on_overlay_click
        )

        self.top_canvas.bind(
            '<Button-3>',
            self.on_top_right_click
        )

        self.bottom_canvas.bind(
            '<Motion>',
            self.on_bottom_motion
        )

        self.bottom_canvas.bind(
            '<Leave>',
            self.on_overlay_leave
        )

        self.bottom_canvas.bind(
            '<Button-1>',
            self.on_bottom_press
        )

        self.bottom_canvas.bind(
            '<B1-Motion>',
            self.on_bottom_drag
        )

        self.bottom_canvas.bind(
            '<ButtonRelease-1>',
            self.on_bottom_release
        )

        self.bottom_canvas.bind(
            '<Button-3>',
            self.on_bottom_right_click
        )

        self.root.update_idletasks()

        self.draw_current_screen(
            10
        )

    # =========================================================
    # CANVAS HELPERS
    # =========================================================

    def reset_canvas_view(self):
        if not self.canvas:
            return

        try:
            self.canvas.yview_moveto(
                0.0
            )

            self.canvas.xview_moveto(
                0.0
            )

        except Exception:
            pass

    def restore_normal_canvas_bindings(self):
        if not self.canvas:
            return

        self.canvas.bind(
            '<Motion>',
            self.on_motion
        )

        self.canvas.bind(
            '<Button-1>',
            self.on_click
        )

        self.canvas.bind(
            '<Leave>',
            self.on_canvas_leave
        )

    def add_image_element(
        self,
        key,
        x,
        y,
        frame
    ):
        item = (
            self.canvas.create_image(
                x,
                y,
                image=self.photo_frames[
                    key
                ][frame],
                anchor='center'
            )
        )

        element = {
            'type':
                'image',

            'key':
                key,

            'item':
                item,

            'frame':
                frame,

            'fade_target':
                frame
        }

        self.screen_elements.append(
            element
        )

        return element

    def add_text_element(
        self,
        x,
        y,
        text,
        frame,
        anchor='center',
        semi_transparent=False,
        font=None
    ):
        if font is None:
            font = (
                self.label_font
            )

        colors = (
            self.text_fade_colors_semi
            if semi_transparent
            else self.text_fade_colors
        )

        item = (
            self.canvas.create_text(
                x,
                y,
                text=text,
                font=font,
                fill=colors[
                    frame
                ],
                anchor=anchor
            )
        )

        element = {
            'type':
                'text',

            'item':
                item,

            'frame':
                frame,

            'fade_target':
                frame,

            'semi':
                semi_transparent
        }

        self.screen_elements.append(
            element
        )

        return element

    def add_highlight(
        self,
        key,
        x,
        y
    ):
        item = (
            self.canvas.create_image(
                x,
                y,
                image=self.photo_frames[
                    key
                ][0],
                anchor='center'
            )
        )

        element = {
            'type':
                'image',

            'key':
                key,

            'item':
                item,

            'frame':
                0,

            'fade_target':
                0,

            'hover_target':
                0,

            'animation_id':
                None,

            'x':
                x,

            'y':
                y,

            'is_highlight':
                True
        }

        self.highlight_items.append(
            element
        )

        self.screen_elements.append(
            element
        )

        width = (
            self.images[
                key
            ].width
        )

        height = (
            self.images[
                key
            ].height
        )

        self.hover_areas.append({
            'left':
                x - width // 2,

            'top':
                y - height // 2,

            'right':
                x + width // 2,

            'bottom':
                y + height // 2
        })

        return element

    # =========================================================
    # DATA: TRANSMISSIONS
    # =========================================================

    def load_transmissions(self):
        self.transmissions_list = []

        if not (
            self.transmissions_dir.exists()
        ):
            return

        for file in (
            self.transmissions_dir.glob(
                '*.txt'
            )
        ):
            filename = (
                file.stem
            )

            parts = (
                filename.split(
                    ' - ',
                    1
                )
            )

            sort_date = None

            if len(parts) == 2:
                date_string = (
                    parts[0].strip()
                )

                title = (
                    parts[1].strip()
                )

                try:
                    date_object = (
                        datetime.strptime(
                            date_string,
                            '%Y-%m-%d'
                        )
                    )

                    formatted_date = (
                        date_object.strftime(
                            '%d.%m.%Y'
                        )
                    )

                    sort_date = (
                        date_object
                    )

                except Exception:
                    formatted_date = (
                        date_string
                    )

            else:
                formatted_date = ''
                title = filename

            self.transmissions_list.append({
                'date':
                    formatted_date,

                'title':
                    title,

                'filepath':
                    file,

                'sort_date':
                    sort_date
            })

        self.transmissions_list.sort(
            key=lambda item: (
                item[
                    'sort_date'
                ] is None,

                item[
                    'sort_date'
                ] or datetime.max,

                item[
                    'title'
                ].lower()
            )
        )

    # =========================================================
    # DATA: BOOKS
    # =========================================================

    def load_books(self):
        self.books_list = []

        if not (
            self.books_dir.exists()
        ):
            return

        for file in (
            self.books_dir.glob(
                '*.fb2'
            )
        ):
            stem = (
                file.stem.strip()
            )

            match = re.match(
                (
                    r'^(.*?)'
                    r'\s*-\s*'
                    r'(\d{4})$'
                ),
                stem
            )

            if match:
                title = (
                    match.group(1).strip()
                )

                date_text = (
                    match.group(2)
                )

                try:
                    year = int(
                        date_text
                    )

                except Exception:
                    year = 9999

            else:
                title = stem
                date_text = ''
                year = 9999

            self.books_list.append({
                'date':
                    date_text,

                'title':
                    title,

                'filepath':
                    file,

                'year':
                    year
            })

        self.books_list.sort(
            key=lambda item: (
                item[
                    'year'
                ],

                item[
                    'title'
                ].lower()
            )
        )

    # =========================================================
    # FILE READING
    # =========================================================

    def read_text_file(
        self,
        path
    ):
        encodings = (
            'utf-8',
            'utf-8-sig',
            'windows-1251'
        )

        last_error = None

        for encoding in encodings:
            try:
                with open(
                    path,
                    'r',
                    encoding=encoding
                ) as file:
                    return file.read()

            except UnicodeDecodeError as error:
                last_error = error

            except Exception as error:
                last_error = error
                break

        if last_error:
            raise last_error

        return ''

    # =========================================================
    # CACHE PLAIN TEXT
    # =========================================================

    def local_xml_tag(
        self,
        tag
    ):
        if '}' in tag:
            return tag.rsplit(
                '}',
                1
            )[1]

        return tag

    def strip_html_for_cache(
        self,
        content
    ):
        if not content:
            return ''

        content = str(
            content
        )

        # Удаляем тяжёлые блоки отдельно.
        # Особенно важен script с __PINIA_STATE__ на Habr.
        for tag in (
            'script',
            'style',
            'noscript',
            'template',
            'svg'
        ):
            try:
                content = re.sub(
                    (
                        r'(?is)<'
                        + tag
                        + r'\b[^>]*>'
                        + r'.*?'
                        + r'</'
                        + tag
                        + r'\s*>'
                    ),
                    '',
                    content
                )
            except Exception:
                pass

        try:
            content = re.sub(
                r'(?is)<head\b[^>]*>.*?</head\s*>',
                '',
                content
            )
        except Exception:
            pass

        # Если есть <article>, для поиска тоже нет смысла
        # индексировать весь интерфейс сайта.
        try:
            articles = re.findall(
                (
                    r'(?is)'
                    r'<article\b[^>]*>'
                    r'.*?'
                    r'</article\s*>'
                ),
                content
            )

            if articles:
                content = max(
                    articles,
                    key=len
                )

        except Exception:
            pass

        content = re.sub(
            r'(?i)<\s*br\s*/?\s*>',
            '\n',
            content
        )

        content = re.sub(
            (
                r'(?i)</\s*'
                r'(p|div|h[1-6]|li|tr|'
                r'blockquote|section|article|'
                r'figcaption|figure)'
                r'\s*>'
            ),
            '\n\n',
            content
        )

        content = re.sub(
            r'(?s)<[^>]+>',
            '',
            content
        )

        content = html.unescape(
            content
        )

        content = (
            content
            .replace(
                '\r\n',
                '\n'
            )
            .replace(
                '\r',
                '\n'
            )
        )

        content = re.sub(
            r'[ \t]+',
            ' ',
            content
        )

        content = re.sub(
            r' *\n *',
            '\n',
            content
        )

        content = re.sub(
            r'\n{3,}',
            '\n\n',
            content
        )

        return (
            content.strip()
        )

    def strip_markdown_for_cache(
        self,
        content
    ):
        content = (
            content
            .replace(
                '\r\n',
                '\n'
            )
            .replace(
                '\r',
                '\n'
            )
        )

        output = []

        token_re = re.compile(
            (
                r'('
                r'\*\*.+?\*\*'
                r'|'
                r'__.+?__'
                r')'
            )
        )

        for raw_line in (
            content.splitlines()
        ):
            line = (
                raw_line.strip()
            )

            line = re.sub(
                r'^#{1,6}\s+',
                '',
                line
            )

            line = re.sub(
                r'^\s*[-*+]\s+',
                '',
                line
            )

            line = re.sub(
                r'^\s*\d+\.\s+',
                '',
                line
            )

            line = re.sub(
                r'\[([^\]]+)\]\([^)]+\)',
                r'\1',
                line
            )

            pieces = (
                token_re.split(
                    line
                )
            )

            clean = []

            for piece in pieces:
                if (
                    (
                        piece.startswith(
                            '**'
                        )
                        and piece.endswith(
                            '**'
                        )
                    )
                    or
                    (
                        piece.startswith(
                            '__'
                        )
                        and piece.endswith(
                            '__'
                        )
                    )
                ):
                    clean.append(
                        piece[2:-2]
                    )

                else:
                    clean.append(
                        piece
                    )

            output.append(
                ''.join(
                    clean
                )
            )

        return (
            '\n'.join(
                output
            ).strip()
        )

    def strip_fb2_for_cache(
        self,
        content
    ):
        try:
            root = (
                ET.fromstring(
                    content
                )
            )

        except Exception:
            cleaned = re.sub(
                r'<[^>]+>',
                ' ',
                content
            )

            cleaned = (
                html.unescape(
                    cleaned
                )
            )

            return re.sub(
                r'\s+',
                ' ',
                cleaned
            ).strip()

        bodies = [
            element
            for element in root.iter()
            if (
                self.local_xml_tag(
                    element.tag
                ) == 'body'
                and not element.attrib.get(
                    'name'
                )
            )
        ]

        if not bodies:
            bodies = [
                element
                for element in root.iter()
                if (
                    self.local_xml_tag(
                        element.tag
                    )
                    == 'body'
                )
            ]

        paragraphs = []

        for body in bodies:
            for element in body.iter():
                tag = (
                    self.local_xml_tag(
                        element.tag
                    )
                )

                if tag in {
                    'p',
                    'subtitle',
                    'text-author',
                    'v'
                }:
                    value = (
                        ' '.join(
                            ''.join(
                                element.itertext()
                            ).split()
                        )
                    )

                    if value:
                        paragraphs.append(
                            value
                        )

        return (
            '\n\n'.join(
                paragraphs
            ).strip()
        )

    def strip_transmission_for_cache(
        self,
        content
    ):
        tc_re = re.compile(
            (
                r'#T='
                r'(\d{2}:\d{2}:\d{2})'
            )
        )

        first = (
            tc_re.search(
                content
            )
        )

        if first:
            content = (
                content[
                    first.start():
                ]
            )

        content = (
            tc_re.sub(
                '',
                content
            )
        )

        paragraphs = []

        for line in (
            content.splitlines()
        ):
            value = (
                line.strip()
            )

            if value:
                paragraphs.append(
                    value
                )

        return (
            '\n\n'.join(
                paragraphs
            )
        )

    def get_plain_text_for_cache(
        self,
        path,
        source_type
    ):
        path = (
            Path(
                path
            )
        )

        try:
            content = (
                self.read_text_file(
                    path
                )
            )

        except Exception:
            return ''

        suffix = (
            path.suffix.lower()
        )

        if suffix == '.fb2':
            return (
                self.strip_fb2_for_cache(
                    content
                )
            )

        if suffix == '.md':
            return (
                self.strip_markdown_for_cache(
                    content
                )
            )

        if suffix in (
            '.html',
            '.htm'
        ):
            return (
                self.strip_html_for_cache(
                    content
                )
            )

        if suffix in (
            '.mhtml',
            '.mht'
        ):
            try:
                message = BytesParser(
                    policy=policy.default
                ).parsebytes(
                    path.read_bytes()
                )

                for part in message.walk():
                    if (
                        part.get_content_type()
                        == 'text/html'
                    ):
                        payload = (
                            part.get_payload(
                                decode=True
                            )
                            or b''
                        )

                        charset = (
                            part.get_content_charset()
                            or 'utf-8'
                        )

                        value = payload.decode(
                            charset,
                            errors='replace'
                        )

                        return (
                            self.strip_html_for_cache(
                                value
                            )
                        )
            except Exception:
                pass

            return ''

        if (
            source_type
            == 'transmission'
        ):
            return (
                self.strip_transmission_for_cache(
                    content
                )
            )

        return content

    # =========================================================
    # CACHE TITLES
    # =========================================================

    def get_cache_title_lines(
        self,
        path,
        source_type
    ):
        path = (
            Path(
                path
            )
        )

        if (
            source_type
            == 'project'
        ):
            return (
                self.get_project_search_title_lines(
                    path
                )
            )

        if (
            source_type
            == 'transmission'
        ):
            stem = (
                path.stem.strip()
            )

            match = re.match(
                (
                    r'^'
                    r'(\d{4}-\d{2}-\d{2})'
                    r'\s*-\s*'
                    r'(.+)$'
                ),
                stem
            )

            if match:
                date_text = (
                    match.group(1)
                )

                title = (
                    match.group(2).strip()
                )

                try:
                    date_text = (
                        datetime.strptime(
                            date_text,
                            '%Y-%m-%d'
                        ).strftime(
                            '%d.%m.%Y'
                        )
                    )

                except Exception:
                    pass

                return [
                    date_text,
                    title
                ]

            return [
                stem
            ]

        if (
            source_type
            == 'book'
        ):
            stem = (
                path.stem.strip()
            )

            match = re.match(
                (
                    r'^(.*?)'
                    r'\s*-\s*'
                    r'(\d{4})$'
                ),
                stem
            )

            if match:
                title = (
                    match.group(1).strip()
                )

                year = (
                    match.group(2)
                )

                return [
                    year,
                    title
                ]

            return [
                stem
            ]

        return [
            path.stem
        ]

    # =========================================================
    # CACHE BUILD
    # =========================================================

    def iter_cache_documents(self):
        self.load_books()
        self.load_transmissions()

        seen = set()

        for item in (
            self.books_list
        ):
            path = (
                Path(
                    item[
                        'filepath'
                    ]
                )
            )

            key = str(
                path
            )

            if key not in seen:
                seen.add(
                    key
                )

                yield (
                    path,
                    'book'
                )

        for item in (
            self.transmissions_list
        ):
            path = (
                Path(
                    item[
                        'filepath'
                    ]
                )
            )

            key = str(
                path
            )

            if key not in seen:
                seen.add(
                    key
                )

                yield (
                    path,
                    'transmission'
                )

        if (
            self.projects_dir.exists()
        ):
            for path in sorted(
                self.projects_dir.iterdir(),
                key=lambda value:
                value.name.lower()
            ):
                if (
                    path.is_file()
                    and
                    path.suffix.lower()
                    in {
                        '.txt',
                        '.fb2',
                        '.md',
                        '.html',
                        '.htm',
                        '.mhtml',
                        '.mht'
                    }
                ):
                    key = str(
                        path
                    )

                    if key not in seen:
                        seen.add(
                            key
                        )

                        yield (
                            path,
                            'project'
                        )

        for value in (
            self.external_files
        ):
            path = (
                Path(
                    value
                )
            )

            if (
                not path.exists()
                or not path.is_file()
            ):
                continue

            if (
                path.suffix.lower()
                not in {
                    '.txt',
                    '.fb2',
                    '.md',
                    '.html',
                    '.htm',
                    '.mhtml',
                    '.mht'
                }
            ):
                continue

            key = str(
                path
            )

            if key not in seen:
                seen.add(
                    key
                )

                yield (
                    path,
                    'external'
                )

    def build_cache_entry(
        self,
        path,
        source_type
    ):
        path = (
            Path(
                path
            )
        )

        try:
            mtime = (
                path.stat().st_mtime_ns
            )

        except Exception:
            mtime = 0

        text = (
            self.get_plain_text_for_cache(
                path,
                source_type
            )
        )

        return {
            'path':
                path,

            'source_type':
                source_type,

            'text':
                text,

            'text_lower':
                text.casefold(),

            'title_lines':
                self.get_cache_title_lines(
                    path,
                    source_type
                ),

            'mtime':
                mtime
        }

    def rebuild_document_cache(self):
        old_cache = (
            self.document_cache
        )

        new_cache = {}

        for (
            path,
            source_type
        ) in (
            self.iter_cache_documents()
        ):
            key = str(
                path
            )

            try:
                mtime = (
                    path.stat().st_mtime_ns
                )

            except Exception:
                mtime = 0

            old = (
                old_cache.get(
                    key
                )
            )

            if (
                old
                and old.get(
                    'mtime'
                ) == mtime
                and old.get(
                    'source_type'
                ) == source_type
            ):
                new_cache[
                    key
                ] = old

            else:
                new_cache[
                    key
                ] = (
                    self.build_cache_entry(
                        path,
                        source_type
                    )
                )

        self.document_cache = (
            new_cache
        )

        self.document_cache_ready = (
            True
        )

        if (
            self.current_screen
            == 'search'
            and len(
                self.global_search_query
            )
            >= self.SEARCH_MIN_CHARS
        ):
            self.rebuild_global_search_results(
                preserve_scroll=True
            )

    def update_document_cache_for_file(
        self,
        path,
        source_type
    ):
        path = (
            Path(
                path
            )
        )

        # При явном обновлении документа сбрасываем его
        # подготовленный Reader cache.
        if hasattr(
            self,
            'reader_document_cache'
        ):
            self.remove_reader_document_cache_for_file(
                path
            )

        if (
            not path.exists()
            or not path.is_file()
        ):
            self.document_cache.pop(
                str(
                    path
                ),
                None
            )

            return

        self.document_cache[
            str(
                path
            )
        ] = (
            self.build_cache_entry(
                path,
                source_type
            )
        )

    def remove_document_from_cache(
        self,
        path
    ):
        self.document_cache.pop(
            str(
                Path(
                    path
                )
            ),
            None
        )

    # =========================================================
    # GLOBAL SEARCH DATA
    # =========================================================

    def parse_search_query(
        self,
        query
    ):
        query = str(
            query or ''
        ).strip()

        if not query:
            return []

        parts = re.split(
            r'\s+OR\s+',
            query,
            flags=re.IGNORECASE
        )

        result = []

        for raw in parts:
            raw = raw.strip()

            if not raw:
                continue

            proximity = re.fullmatch(
                r'(.+?)\s*=\s*(\d+)\s*',
                raw
            )

            if proximity:
                raw_words = re.findall(
                    r'!?\w+',
                    proximity.group(1),
                    flags=re.UNICODE
                )

                if len(raw_words) >= 2:
                    words = []

                    for value in raw_words:
                        exact = (
                            value.startswith('!')
                        )

                        word = (
                            value[1:]
                            if exact
                            else value
                        )

                        if not word:
                            continue

                        words.append({
                            'value':
                                word.casefold(),

                            'exact':
                                exact
                        })

                    if len(words) >= 2:
                        result.append({
                            'type':
                                'proximity',

                            'words':
                                words,

                            'gap':
                                max(
                                    0,
                                    min(
                                        100,
                                        int(
                                            proximity.group(2)
                                        )
                                    )
                                )
                        })

                        continue

            exact_literal = re.fullmatch(
                r'!(\w+)',
                raw,
                flags=re.UNICODE
            )

            if exact_literal:
                result.append({
                    'type':
                        'exact_word',

                    'value':
                        exact_literal.group(1).casefold()
                })

                continue

            result.append({
                'type':
                    'literal',

                'value':
                    raw
            })

        return result

    def find_query_matches(
        self,
        text,
        query
    ):
        """
        Return merged (start, end) spans in original text.
        """

        alternatives = (
            self.parse_search_query(
                query
            )
        )

        if not alternatives:
            return []

        matches = []

        word_tokens = None

        for alternative in alternatives:

            if alternative['type'] == 'literal':
                value = alternative['value']

                if not value:
                    continue

                try:
                    for match in re.finditer(
                        re.escape(value),
                        text,
                        flags=re.IGNORECASE
                    ):
                        matches.append(
                            (
                                match.start(),
                                match.end()
                            )
                        )

                except Exception:
                    pass

                continue

            if alternative['type'] == 'exact_word':
                value = alternative['value']

                if not value:
                    continue

                try:
                    pattern = (
                        r'(?<!\w)'
                        + re.escape(value)
                        + r'(?!\w)'
                    )

                    for match in re.finditer(
                        pattern,
                        text,
                        flags=re.IGNORECASE | re.UNICODE
                    ):
                        matches.append(
                            (
                                match.start(),
                                match.end()
                            )
                        )

                except Exception:
                    pass

                continue

            # ---------------------------------------------
            # Proximity search.
            # ---------------------------------------------

            if word_tokens is None:
                word_tokens = [
                    (
                        match.start(),
                        match.end(),
                        match.group(0).casefold()
                    )
                    for match in re.finditer(
                        r'\w+',
                        text,
                        flags=re.UNICODE
                    )
                ]

            wanted = alternative[
                'words'
            ]

            gap = alternative[
                'gap'
            ]

            if not wanted:
                continue

            def token_matches(
                token_value,
                wanted_item
            ):
                wanted_value = (
                    wanted_item['value']
                )

                if wanted_item.get(
                    'exact',
                    False
                ):
                    return (
                        token_value
                        == wanted_value
                    )

                # Для proximity обычное слово считается
                # началом слова. Поэтому:
                # птиц -> птиц, птицы, птицами...
                return token_value.startswith(
                    wanted_value
                )

            for index, token in enumerate(
                word_tokens
            ):
                if not token_matches(
                    token[2],
                    wanted[0]
                ):
                    continue

                current = index
                last = index
                valid = True

                for wanted_word in wanted[1:]:
                    found = None

                    # At most gap words BETWEEN keywords.
                    stop = min(
                        len(word_tokens),
                        current + gap + 2
                    )

                    for candidate in range(
                        current + 1,
                        stop
                    ):
                        if token_matches(
                            word_tokens[
                                candidate
                            ][2],
                            wanted_word
                        ):
                            found = candidate
                            break

                    if found is None:
                        valid = False
                        break

                    current = found
                    last = found

                if valid:
                    matches.append(
                        (
                            token[0],
                            word_tokens[
                                last
                            ][1]
                        )
                    )

        if not matches:
            return []

        matches.sort(
            key=lambda item:
            (
                item[0],
                item[1]
            )
        )

        # Remove exact duplicates, but do not merge
        # neighbouring search hits.
        result = []

        seen = set()

        for item in matches:
            if item not in seen:
                seen.add(item)
                result.append(item)

        return result

    def is_search_path_excluded(
        self,
        path
    ):
        return (
            str(
                Path(path)
            )
            in self.search_excluded_paths
        )

    def set_search_path_excluded(
        self,
        path,
        excluded
    ):
        key = str(
            Path(path)
        )

        if excluded:
            self.search_excluded_paths.add(
                key
            )
        else:
            self.search_excluded_paths.discard(
                key
            )

        self.factory_reset_pending = False
        self.save_settings()

        if (
            self.current_screen == 'search'
            and len(
                self.global_search_query
            ) >= self.SEARCH_MIN_CHARS
        ):
            self.rebuild_global_search_results(
                preserve_scroll=False
            )

    def include_all_search_documents(self):
        if not self.search_excluded_paths:
            return

        self.search_excluded_paths.clear()

        self.factory_reset_pending = False
        self.save_settings()

        if (
            self.current_screen == 'search'
            and len(
                self.global_search_query
            ) >= self.SEARCH_MIN_CHARS
        ):
            self.rebuild_global_search_results(
                preserve_scroll=False
            )

    def cache_source_group(
        self,
        source_type
    ):
        return {
            'book':
                'books',

            'transmission':
                'transmissions',

            'project':
                'projects',

            'external':
                'files'
        }.get(
            source_type
        )

    def global_group_enabled(
        self,
        source_type
    ):
        group = (
            self.cache_source_group(
                source_type
            )
        )

        if not group:
            return False

        return bool(
            self.global_search_groups.get(
                group,
                False
            )
        )

    def rebuild_global_search_results(
        self,
        preserve_scroll=False
    ):
        if (
            preserve_scroll
            and self.global_search_canvas
        ):
            try:
                view = self.global_search_canvas.yview()

                if view:
                    self.global_search_saved_yview = (
                        float(view[0])
                    )
            except Exception:
                pass

        self.global_search_results = []

        query = (
            self.global_search_query
        )

        if (
            len(query.strip())
            < self.SEARCH_MIN_CHARS
        ):
            self.global_search_page = 0
            self.update_global_search_count()

            if self.current_screen == 'search':
                self.render_global_search_results(
                    restore_scroll=False
                )

            return

        for entry in self.document_cache.values():

            if not self.global_group_enabled(
                entry['source_type']
            ):
                continue

            if self.is_search_path_excluded(
                entry['path']
            ):
                continue

            source_text = (
                entry.get(
                    'text',
                    ''
                )
                or ''
            )

            matches = (
                self.find_query_matches(
                    source_text,
                    query
                )
            )

            for start, end in matches:
                self.global_search_results.append({
                    'path':
                        entry['path'],

                    'source_type':
                        entry['source_type'],

                    'position':
                        start,

                    'end':
                        end,

                    'text':
                        source_text,

                    'title_lines':
                        list(
                            entry[
                                'title_lines'
                            ]
                        )
                })

        page_count = (
            self.get_global_search_page_count()
        )

        self.global_search_page = max(
            0,
            min(
                self.global_search_page,
                page_count - 1
            )
        )

        self.update_global_search_count()

        if self.current_screen == 'search':
            self.render_global_search_results(
                restore_scroll=preserve_scroll
            )

    def get_global_search_page_count(self):
        total = len(
            self.global_search_results
        )

        if total <= 0:
            return 1

        return (
            (
                total
                + self.GLOBAL_RESULTS_PER_PAGE
                - 1
            )
            // self.GLOBAL_RESULTS_PER_PAGE
        )

    def get_global_page_results(self):
        start = (
            self.global_search_page
            * self.GLOBAL_RESULTS_PER_PAGE
        )

        end = (
            start
            + self.GLOBAL_RESULTS_PER_PAGE
        )

        return (
            self.global_search_results[
                start:end
            ]
        )

    def global_search_previous_page(self):
        if (
            self.global_search_page
            <= 0
        ):
            return

        self.global_search_page -= 1

        self.global_search_saved_yview = 0.0

        self.render_global_search_results(
            restore_scroll=False
        )

    def global_search_next_page(self):
        if (
            self.global_search_page + 1
            >= self.get_global_search_page_count()
        ):
            return

        self.global_search_page += 1

        self.global_search_saved_yview = 0.0

        self.render_global_search_results(
            restore_scroll=False
        )

    # =========================================================
    # GLOBAL SEARCH EXCERPT
    # =========================================================

    def get_global_result_excerpt(
        self,
        result
    ):
        text = (
            result[
                'text'
            ]
        )

        match_start = (
            int(
                result[
                    'position'
                ]
            )
        )

        match_end = (
            int(
                result[
                    'end'
                ]
            )
        )

        # Не изменяем текст после расчёта позиции:
        # благодаря этому индексы совпадения
        # остаются абсолютно точными.
        before_chars = 650
        after_chars = 650

        left = max(
            0,
            match_start
            - before_chars
        )

        right = min(
            len(
                text
            ),
            match_end
            + after_chars
        )

        # Стараемся начинать с границы слова.
        if left > 0:
            while (
                left < match_start
                and not text[
                    left
                ].isspace()
            ):
                left += 1

            while (
                left < match_start
                and text[
                    left
                ].isspace()
            ):
                left += 1

        # И заканчивать после целого слова.
        if (
            right
            < len(
                text
            )
        ):
            while (
                right < len(
                    text
                )
                and not text[
                    right
                ].isspace()
            ):
                right += 1

        excerpt = (
            text[
                left:right
            ]
        )

        local_start = (
            match_start - left
        )

        local_end = (
            match_end - left
        )

        return (
            excerpt,
            local_start,
            local_end
        )

    # =========================================================
    # END PART 1/4
    # PART 2 STARTS WITH GLOBAL SEARCH UI
    # =========================================================
    # =========================================================
    # GLOBAL SEARCH UI
    # =========================================================

    def destroy_global_search_widgets(self):
        if self.global_search_entry:
            try:
                self.global_search_entry.destroy()
            except Exception:
                pass

            self.global_search_entry = None

        if self.global_search_scrollbar:
            try:
                self.global_search_scrollbar.destroy()
            except Exception:
                pass

            self.global_search_scrollbar = None

        if self.global_search_canvas:
            try:
                self.global_search_canvas.destroy()
            except Exception:
                pass

            self.global_search_canvas = None

        self.global_search_content_frame = None
        self.global_search_window_item = None

        self.global_search_result_items = []
        self.global_search_checkbox_items = []

        self.global_search_hover_index = None

    def draw_global_search_screen(
        self,
        preserve_scroll=False
    ):
        if (
            preserve_scroll
            and self.global_search_canvas
        ):
            try:
                view = (
                    self.global_search_canvas.yview()
                )

                if view:
                    self.global_search_saved_yview = (
                        float(
                            view[0]
                        )
                    )

            except Exception:
                pass

        self.destroy_global_search_widgets()

        self.canvas.delete(
            'all'
        )

        self.canvas.configure(
            bg=self.bg_color()
        )

        self.scrollbar.pack_forget()

        width = max(
            1,
            self.canvas.winfo_width()
        )

        height = max(
            1,
            self.canvas.winfo_height()
        )

        self.canvas.config(
            scrollregion=(
                0,
                0,
                width,
                height
            )
        )

        self.screen_elements = []
        self.highlight_items = []
        self.hover_areas = []

        self.global_search_result_items = []
        self.global_search_checkbox_items = []

        self.global_search_hover_index = None

        # -----------------------------------------------------
        # Fixed search field
        # -----------------------------------------------------

        local_search_y = (
            self.GLOBAL_SEARCH_Y
            - self.TOP_BAR_HEIGHT
        )

        local_checkbox_y = (
            self.GLOBAL_CHECKBOX_Y
            - self.TOP_BAR_HEIGHT
        )

        center_x = (
            width // 2
        )

        self.global_search_box_item = (
            self.canvas.create_image(
                center_x,
                local_search_y,
                image=self.photo_frames[
                    '30'
                ][10],
                anchor='center'
            )
        )

        box_left = (
            center_x
            - self.SEARCH_BOX_WIDTH // 2
        )

        box_right = (
            center_x
            + self.SEARCH_BOX_WIDTH // 2
        )

        counter_width = 65

        entry_width = max(
            80,
            self.SEARCH_BOX_WIDTH
            - self.SEARCH_TEXT_LEFT
            - counter_width
            - self.SEARCH_TEXT_RIGHT
        )

        self.global_search_entry = tk.Entry(
            self.canvas,
            font=(
                'Alice',
                12
            ),
            bd=0,
            relief=tk.FLAT,
            highlightthickness=0,
            bg=self.bg_color(),
            fg=self.text_color(),
            insertbackground=(
                self.text_color()
            )
        )

        self.global_search_entry.insert(
            0,
            self.global_search_query
        )

        self.global_search_entry.place(
            x=(
                box_left
                + self.SEARCH_TEXT_LEFT
            ),
            y=(
                local_search_y - 11
            ),
            width=entry_width,
            height=22
        )

        self.global_search_entry.bind(
            '<KeyRelease>',
            self.on_global_search_key_release
        )

        self.global_search_entry.bind(
            '<Control-KeyPress>',
            self.on_global_search_ctrl_key
        )

        self.global_search_entry.bind(
            '<Button-3>',
            self.show_global_search_context_menu
        )

        self.global_search_count_item = (
            self.canvas.create_text(
                box_right
                - self.SEARCH_TEXT_RIGHT,
                local_search_y,
                text='',
                font=(
                    'Alice',
                    11
                ),
                fill=self.secondary_color(),
                anchor='e'
            )
        )

        # -----------------------------------------------------
        # Fixed checkboxes
        # -----------------------------------------------------

        checkbox_font = tkfont.Font(
            family='Alice',
            size=self.font_size
        )

        groups = [
            (
                'books',
                'Книги'
            ),
            (
                'transmissions',
                'Передачи'
            ),
            (
                'projects',
                'Проекты'
            ),
            (
                'files',
                'Файлы'
            )
        ]

        group_widths = []

        for key, label in groups:
            group_widths.append(
                self.GLOBAL_CHECKBOX_SIZE
                + self.GLOBAL_CHECKBOX_TEXT_GAP
                + checkbox_font.measure(
                    label
                )
            )

        total_width = (
            sum(
                group_widths
            )
            + self.GLOBAL_CHECKBOX_GROUP_GAP
            * (
                len(groups) - 1
            )
        )

        x = (
            center_x
            - total_width // 2
        )

        for index, (
            key,
            label
        ) in enumerate(
            groups
        ):
            checkbox_x = (
                x
                + self.GLOBAL_CHECKBOX_SIZE // 2
            )

            image_key = (
                '39'
                if self.global_search_groups.get(
                    key,
                    True
                )
                else '38'
            )

            image_item = (
                self.canvas.create_image(
                    checkbox_x,
                    local_checkbox_y,
                    image=self.photo_frames[
                        image_key
                    ][10],
                    anchor='center'
                )
            )

            text_x = (
                x
                + self.GLOBAL_CHECKBOX_SIZE
                + self.GLOBAL_CHECKBOX_TEXT_GAP
            )

            text_item = (
                self.canvas.create_text(
                    text_x,
                    local_checkbox_y,
                    text=label,
                    font=self.label_font,
                    fill=self.text_color(),
                    anchor='w'
                )
            )

            group_width = (
                group_widths[
                    index
                ]
            )

            self.global_search_checkbox_items.append({
                'key':
                    key,

                'image_item':
                    image_item,

                'text_item':
                    text_item,

                'left':
                    x,

                'right':
                    x + group_width,

                'top':
                    local_checkbox_y
                    - self.GLOBAL_CHECKBOX_SIZE // 2,

                'bottom':
                    local_checkbox_y
                    + self.GLOBAL_CHECKBOX_SIZE // 2
            })

            x += (
                group_width
                + self.GLOBAL_CHECKBOX_GROUP_GAP
            )

        # -----------------------------------------------------
        # Scrollable result canvas
        # -----------------------------------------------------

        local_results_top = (
            self.GLOBAL_RESULTS_TOP
            - self.TOP_BAR_HEIGHT
        )

        result_height = max(
            40,
            height - local_results_top
        )

        self.global_search_canvas = Canvas(
            self.canvas,
            bg=self.bg_color(),
            highlightthickness=0,
            borderwidth=0
        )

        self.global_search_canvas.place(
            x=0,
            y=local_results_top,
            width=width,
            height=result_height
        )

        self.global_search_scrollbar = Scrollbar(
            self.canvas,
            orient=tk.VERTICAL,
            command=(
                self.global_search_canvas.yview
            )
        )

        self.global_search_canvas.configure(
            yscrollcommand=(
                self.global_search_scrollbar.set
            )
        )

        self.global_search_content_frame = Frame(
            self.global_search_canvas,
            bg=self.bg_color(),
            highlightthickness=0,
            bd=0
        )

        self.global_search_window_item = (
            self.global_search_canvas.create_window(
                0,
                0,
                window=(
                    self.global_search_content_frame
                ),
                anchor='nw'
            )
        )

        self.global_search_content_frame.bind(
            '<Configure>',
            self.on_global_search_content_configure
        )

        self.global_search_canvas.bind(
            '<Configure>',
            self.on_global_search_canvas_configure
        )

        for widget in (
            self.global_search_canvas,
            self.global_search_content_frame
        ):
            widget.bind(
                '<MouseWheel>',
                self.on_global_search_mousewheel
            )

            widget.bind(
                '<Button-4>',
                self.on_global_search_mousewheel
            )

            widget.bind(
                '<Button-5>',
                self.on_global_search_mousewheel
            )

        self.canvas.bind(
            '<Button-1>',
            self.on_global_search_canvas_click
        )

        self.update_global_search_count()

        self.render_global_search_results(
            restore_scroll=(
                preserve_scroll
            )
        )

        if self.global_search_entry:
            self.global_search_entry.focus_set()

            self.global_search_entry.icursor(
                tk.END
            )

    def on_global_search_content_configure(
        self,
        event=None
    ):
        if not self.global_search_canvas:
            return

        try:
            bbox = (
                self.global_search_canvas.bbox(
                    'all'
                )
            )

            if bbox:
                self.global_search_canvas.configure(
                    scrollregion=bbox
                )

        except Exception:
            pass

    def on_global_search_canvas_configure(
        self,
        event
    ):
        if (
            not self.global_search_canvas
            or self.global_search_window_item
            is None
        ):
            return

        # Критично: content frame всегда получает
        # фактическую ширину canvas. Поэтому после возврата
        # из reader карточки сразу остаются по центру.
        try:
            self.global_search_canvas.itemconfigure(
                self.global_search_window_item,
                width=event.width
            )

            self.root.after_idle(
                self.recenter_global_search_cards
            )

        except Exception:
            pass

    def recenter_global_search_cards(self):
        if not self.global_search_canvas:
            return

        width = (
            self.global_search_canvas.winfo_width()
        )

        geometry = (
            self.get_global_result_card_geometry()
        )

        cards_width = geometry[
            'total_width'
        ]

        card_height = geometry[
            'height'
        ]

        left = max(
            0,
            (
                width
                - cards_width
            ) // 2
        )

        for item in (
            self.global_search_result_items
        ):
            holder = item.get(
                'holder'
            )

            if holder:
                try:
                    holder.place_configure(
                        x=left,
                        width=cards_width,
                        height=card_height
                    )

                except Exception:
                    pass

    def on_global_search_root_mousewheel(
        self,
        event
    ):
        if (
            self.current_screen != 'search'
            or not self.global_search_canvas
        ):
            return

        return self.on_global_search_mousewheel(
            event
        )

    def on_global_search_page_key(
        self,
        event
    ):
        if (
            self.current_screen != 'search'
            or not self.global_search_canvas
        ):
            return

        try:
            if event.keysym == 'Prior':
                self.global_search_canvas.yview_scroll(
                    -1,
                    'pages'
                )

            elif event.keysym == 'Next':
                self.global_search_canvas.yview_scroll(
                    1,
                    'pages'
                )

            else:
                return

        except Exception:
            pass

        return 'break'

    def on_global_search_mousewheel(
        self,
        event
    ):
        if not self.global_search_canvas:
            return 'break'

        if (
            getattr(
                event,
                'num',
                None
            ) == 5
            or getattr(
                event,
                'delta',
                0
            ) < 0
        ):
            self.global_search_canvas.yview_scroll(
                3,
                'units'
            )

        elif (
            getattr(
                event,
                'num',
                None
            ) == 4
            or getattr(
                event,
                'delta',
                0
            ) > 0
        ):
            self.global_search_canvas.yview_scroll(
                -3,
                'units'
            )

        return 'break'

    def get_global_search_count_text(self):
        if (
            len(
                self.global_search_query
            )
            < self.SEARCH_MIN_CHARS
        ):
            return ''

        return str(
            len(
                self.global_search_results
            )
        )

    def update_global_search_count(self):
        if (
            self.global_search_count_item
            is None
        ):
            return

        try:
            self.canvas.itemconfig(
                self.global_search_count_item,
                text=(
                    self.get_global_search_count_text()
                ),
                fill=self.secondary_color()
            )

        except Exception:
            pass

    def cancel_global_search_debounce(self):
        timer = getattr(
            self,
            'global_search_debounce_timer',
            None
        )

        if timer is not None:
            try:
                self.root.after_cancel(
                    timer
                )
            except Exception:
                pass

        self.global_search_debounce_timer = None

    def schedule_global_search_debounce(self):
        # Каждое новое изменение начинает отсчёт заново.
        self.cancel_global_search_debounce()

        # Пока пользователь печатает, старые результаты
        # больше не соответствуют строке поиска.
        self.global_search_results = []
        self.global_search_page = 0
        self.global_search_saved_yview = 0.0

        self.update_global_search_count()

        if (
            self.current_screen == 'search'
            and self.global_search_content_frame
        ):
            self.render_global_search_results(
                restore_scroll=False
            )

        # Для строки короче минимальной длины поиск
        # вообще не планируем.
        if (
            len(self.global_search_query)
            < self.SEARCH_MIN_CHARS
        ):
            return

        self.global_search_debounce_timer = (
            self.root.after(
                self.global_search_debounce_delay,
                self.run_debounced_global_search
            )
        )

    def run_debounced_global_search(self):
        self.global_search_debounce_timer = None

        if self.current_screen != 'search':
            return

        if (
            len(self.global_search_query)
            < self.SEARCH_MIN_CHARS
        ):
            return

        # Сам rebuild ищет по document_cache,
        # то есть по уже находящемуся в RAM тексту.
        self.rebuild_global_search_results(
            preserve_scroll=False
        )

    def on_global_search_key_release(
        self,
        event=None
    ):
        if not self.global_search_entry:
            return

        if (
            event is not None
            and event.keysym in (
                'Shift_L',
                'Shift_R',
                'Control_L',
                'Control_R',
                'Alt_L',
                'Alt_R',
                'Left',
                'Right',
                'Up',
                'Down',
                'Home',
                'End',
                'Prior',
                'Next'
            )
        ):
            return

        value = (
            self.global_search_entry.get()
        )

        if (
            value
            == self.global_search_query
        ):
            return

        self.global_search_query = value

        # Никакого поиска сейчас.
        # Только запускаем/перезапускаем 2-секундный таймер.
        self.schedule_global_search_debounce()

    def global_search_copy(self):
        if not self.global_search_entry:
            return

        try:
            if not self.global_search_entry.selection_present():
                return

            first = self.global_search_entry.index(
                tk.SEL_FIRST
            )

            last = self.global_search_entry.index(
                tk.SEL_LAST
            )

            value = self.global_search_entry.get()[
                first:last
            ]

            self.root.clipboard_clear()
            self.root.clipboard_append(
                value
            )

        except Exception:
            pass

    def global_search_cut(self):
        if not self.global_search_entry:
            return

        try:
            if not self.global_search_entry.selection_present():
                return

            first = self.global_search_entry.index(
                tk.SEL_FIRST
            )

            last = self.global_search_entry.index(
                tk.SEL_LAST
            )

            value = self.global_search_entry.get()[
                first:last
            ]

            self.root.clipboard_clear()
            self.root.clipboard_append(
                value
            )

            self.global_search_entry.delete(
                first,
                last
            )

            self.global_search_query = (
                self.global_search_entry.get()
            )

            self.schedule_global_search_debounce()

        except Exception:
            pass

    def on_global_search_ctrl_key(
        self,
        event
    ):
        code = getattr(
            event,
            'keycode',
            None
        )

        char = (
            getattr(
                event,
                'char',
                ''
            ) or ''
        ).lower()

        # Virtual-key codes Windows:
        # A=65 C=67 V=86 X=88.
        # Они не зависят от RU/EN раскладки.
        if code == 65 or char in ('a', 'ф'):
            if self.global_search_entry:
                self.global_search_entry.selection_range(
                    0,
                    tk.END
                )

                self.global_search_entry.icursor(
                    tk.END
                )

            return 'break'

        if code == 67 or char in ('c', 'с'):
            self.global_search_copy()
            return 'break'

        if code == 88 or char in ('x', 'ч'):
            self.global_search_cut()
            return 'break'

        if code == 86 or char in ('v', 'м'):
            return self.paste_into_global_search(
                event
            )

    def show_global_search_context_menu(
        self,
        event
    ):
        if not self.global_search_entry:
            return 'break'

        menu = Menu(
            self.global_search_entry,
            tearoff=0
        )

        selected = False

        try:
            selected = (
                self.global_search_entry.selection_present()
            )
        except Exception:
            pass

        menu.add_command(
            label='Вырезать',
            command=self.global_search_cut,
            state=(
                tk.NORMAL
                if selected
                else tk.DISABLED
            )
        )

        menu.add_command(
            label='Копировать',
            command=self.global_search_copy,
            state=(
                tk.NORMAL
                if selected
                else tk.DISABLED
            )
        )

        menu.add_command(
            label='Вставить',
            command=self.paste_into_global_search
        )

        try:
            menu.tk_popup(
                event.x_root,
                event.y_root
            )

        finally:
            menu.grab_release()

        return 'break'

    def paste_into_global_search(
        self,
        event=None
    ):
        if not self.global_search_entry:
            return 'break'

        try:
            value = (
                self.root.clipboard_get()
            )

        except tk.TclError:
            return 'break'

        try:
            if (
                self.global_search_entry
                .selection_present()
            ):
                first = (
                    self.global_search_entry.index(
                        tk.SEL_FIRST
                    )
                )

                last = (
                    self.global_search_entry.index(
                        tk.SEL_LAST
                    )
                )

                self.global_search_entry.delete(
                    first,
                    last
                )

        except Exception:
            pass

        position = (
            self.global_search_entry.index(
                tk.INSERT
            )
        )

        self.global_search_entry.insert(
            position,
            value
        )

        self.global_search_query = (
            self.global_search_entry.get()
        )

        # Paste считается обычным изменением строки:
        # отсчёт 2 секунд начинается заново.
        self.schedule_global_search_debounce()

        return 'break'

    def on_global_search_canvas_click(
        self,
        event
    ):
        for item in (
            self.global_search_checkbox_items
        ):
            if (
                item['left']
                <= event.x
                <= item['right']
                and
                item['top']
                <= event.y
                <= item['bottom']
            ):
                self.toggle_global_search_group(
                    item['key']
                )

                return 'break'

    def toggle_global_search_group(
        self,
        key
    ):
        if (
            key
            not in self.global_search_groups
        ):
            return

        self.global_search_groups[
            key
        ] = (
            not self.global_search_groups[
                key
            ]
        )

        self.save_settings()

        for item in (
            self.global_search_checkbox_items
        ):
            if item['key'] != key:
                continue

            image_key = (
                '39'
                if self.global_search_groups[
                    key
                ]
                else '38'
            )

            try:
                self.canvas.itemconfig(
                    item[
                        'image_item'
                    ],
                    image=self.photo_frames[
                        image_key
                    ][10]
                )

            except Exception:
                pass

            break

        self.global_search_page = 0
        self.global_search_saved_yview = 0.0

        self.cancel_global_search_debounce()

        self.rebuild_global_search_results(
            preserve_scroll=False
        )

    # =========================================================
    # GLOBAL SEARCH RESULT CARD
    # =========================================================

    def bind_global_result_widget(
        self,
        widget,
        index
    ):
        widget.bind(
            '<Enter>',
            lambda event,
            value=index:
            self.set_global_search_hover(
                value
            )
        )

        widget.bind(
            '<Leave>',
            lambda event:
            self.root.after(
                1,
                self.recheck_global_search_hover
            )
        )

        widget.bind(
            '<Button-1>',
            lambda event,
            value=index:
            self.open_global_search_result(
                value
            )
        )

        widget.bind(
            '<MouseWheel>',
            self.on_global_search_mousewheel
        )

        widget.bind(
            '<Button-4>',
            self.on_global_search_mousewheel
        )

        widget.bind(
            '<Button-5>',
            self.on_global_search_mousewheel
        )

    def recheck_global_search_hover(self):
        try:
            pointer_x = (
                self.root.winfo_pointerx()
            )

            pointer_y = (
                self.root.winfo_pointery()
            )

            widget = (
                self.root.winfo_containing(
                    pointer_x,
                    pointer_y
                )
            )

        except Exception:
            widget = None

        current = widget

        while current is not None:
            for index, item in enumerate(
                self.global_search_result_items
            ):
                if (
                    current
                    in item[
                        'widgets'
                    ]
                ):
                    self.set_global_search_hover(
                        index
                    )

                    return

            try:
                current = (
                    current.master
                )

            except Exception:
                break

        self.set_global_search_hover(
            None
        )

    def set_global_search_hover(
        self,
        index
    ):
        if (
            index
            == self.global_search_hover_index
        ):
            return

        old = (
            self.global_search_hover_index
        )

        if (
            old is not None
            and old < len(
                self.global_search_result_items
            )
        ):
            item = self.global_search_result_items[
                old
            ]

            for frame in item.get(
                'border_frames',
                []
            ):
                try:
                    frame.configure(
                        bg=self.bg_color()
                    )
                except Exception:
                    pass

        self.global_search_hover_index = index

        if (
            index is not None
            and index < len(
                self.global_search_result_items
            )
        ):
            item = self.global_search_result_items[
                index
            ]

            for frame in item.get(
                'border_frames',
                []
            ):
                try:
                    frame.configure(
                        bg=self.GLOBAL_RESULT_BORDER
                    )
                except Exception:
                    pass

    def center_excerpt_on_match(
        self,
        widget,
        match_start
    ):
        # Глобальные excerpts теперь рисуются Canvas'ом.
        # Scrollable Text здесь больше не используется.
        return

    def get_global_result_card_geometry(self):
        # Реальная ширина области результатов.
        try:
            available = (
                self.global_search_canvas.winfo_width()
            )
        except Exception:
            available = 1

        if available <= 2:
            try:
                available = self.canvas.winfo_width()
            except Exception:
                available = 1000

        # Поля слева и справа.
        outer_margin = 28

        usable = max(
            300,
            available - outer_margin * 2
        )

        # На широком экране оставляем первоначальные размеры.
        normal_total = (
            self.GLOBAL_RESULT_TITLE_WIDTH
            + self.GLOBAL_RESULT_GAP
            + self.GLOBAL_RESULT_TEXT_WIDTH
        )

        if usable >= normal_total:
            return {
                'title_width':
                    self.GLOBAL_RESULT_TITLE_WIDTH,

                'text_width':
                    self.GLOBAL_RESULT_TEXT_WIDTH,

                'gap':
                    self.GLOBAL_RESULT_GAP,

                'height':
                    self.GLOBAL_RESULT_HEIGHT,

                'total_width':
                    normal_total
            }

        # -----------------------------------------------------
        # Узкое окно.
        #
        # Gap постепенно уменьшается.
        # Левая колонка получает около 35%, правая 65%.
        # -----------------------------------------------------

        gap = max(
            18,
            min(
                self.GLOBAL_RESULT_GAP,
                int(usable * 0.05)
            )
        )

        columns = max(
            240,
            usable - gap
        )

        title_width = int(
            columns * 0.35
        )

        text_width = (
            columns - title_width
        )

        # Минимумы применяем только пока они физически
        # помещаются. Карточка никогда не должна быть
        # шире окна.
        if columns >= 520:
            title_width = max(
                180,
                title_width
            )

            text_width = (
                columns - title_width
            )

        title_width = max(
            80,
            title_width
        )

        text_width = max(
            140,
            columns - title_width
        )

        # Если из-за hard minimum вышли за available,
        # окончательно clamp.
        total = (
            title_width
            + gap
            + text_width
        )

        if total > usable:
            overflow = (
                total - usable
            )

            remove_right = min(
                overflow,
                max(
                    0,
                    text_width - 100
                )
            )

            text_width -= (
                remove_right
            )

            overflow -= (
                remove_right
            )

            if overflow:
                title_width = max(
                    60,
                    title_width - overflow
                )

        total = (
            title_width
            + gap
            + text_width
        )

        # Чем сильнее карточка ужалась по ширине,
        # тем выше она становится.
        compression = max(
            0.0,
            1.0
            - total
            / float(
                normal_total
            )
        )

        height = int(
            self.GLOBAL_RESULT_HEIGHT
            + compression * 150
        )

        height = max(
            self.GLOBAL_RESULT_HEIGHT,
            min(
                350,
                height
            )
        )

        return {
            'title_width':
                title_width,

            'text_width':
                text_width,

            'gap':
                gap,

            'height':
                height,

            'total_width':
                total
        }

    def wrap_global_excerpt_lines(
        self,
        text,
        max_width
    ):
        """
        Возвращает visual lines.

        У каждой строки сохраняются абсолютные смещения
        относительно excerpt, поэтому подсветка найденного
        фрагмента остаётся точной.
        """

        font = tkfont.Font(
            family=self.content_font_family,
            size=self.reader_font_size
        )

        max_width = max(
            20,
            int(max_width)
        )

        lines = []

        n = len(text)
        position = 0

        while position < n:
            # ---------------------------------------------
            # Явный перевод строки.
            # ---------------------------------------------

            if text[position] == '\n':
                lines.append({
                    'start':
                        position,

                    'end':
                        position,

                    'text':
                        ''
                })

                position += 1
                continue

            paragraph_end = text.find(
                '\n',
                position
            )

            if paragraph_end < 0:
                paragraph_end = n

            line_start = position

            # Пробелы в самом начале visual line
            # не должны сдвигать текст вправо.
            while (
                line_start < paragraph_end
                and text[line_start] in ' \t'
            ):
                line_start += 1

            if line_start >= paragraph_end:
                lines.append({
                    'start':
                        line_start,

                    'end':
                        line_start,

                    'text':
                        ''
                })

                position = (
                    paragraph_end + 1
                    if paragraph_end < n
                    else paragraph_end
                )

                continue

            # ---------------------------------------------
            # Binary search максимально длинного куска,
            # помещающегося по ширине.
            # ---------------------------------------------

            lo = line_start + 1
            hi = paragraph_end
            best = line_start + 1

            while lo <= hi:
                mid = (
                    lo + hi
                ) // 2

                value = text[
                    line_start:mid
                ]

                if font.measure(value) <= max_width:
                    best = mid
                    lo = mid + 1

                else:
                    hi = mid - 1

            # Весь остаток paragraph помещается.
            if best >= paragraph_end:
                visible_end = paragraph_end

                while (
                    visible_end > line_start
                    and text[
                        visible_end - 1
                    ] in ' \t'
                ):
                    visible_end -= 1

                lines.append({
                    'start':
                        line_start,

                    'end':
                        visible_end,

                    'text':
                        text[
                            line_start:visible_end
                        ]
                })

                position = (
                    paragraph_end + 1
                    if paragraph_end < n
                    else paragraph_end
                )

                continue

            # ---------------------------------------------
            # Ищем границу слова.
            # ---------------------------------------------

            cut = best

            while (
                cut > line_start
                and not text[
                    cut - 1
                ].isspace()
            ):
                cut -= 1

            # Очень длинное слово.
            if cut <= line_start:
                cut = best

            visible_end = cut

            while (
                visible_end > line_start
                and text[
                    visible_end - 1
                ] in ' \t'
            ):
                visible_end -= 1

            lines.append({
                'start':
                    line_start,

                'end':
                    visible_end,

                'text':
                    text[
                        line_start:visible_end
                    ]
            })

            position = cut

            while (
                position < paragraph_end
                and text[position] in ' \t'
            ):
                position += 1

        return lines

    def get_global_excerpt_visible_lines(
        self,
        excerpt,
        local_start,
        local_end,
        text_width,
        text_height
    ):
        """
        Выбирает строго целое количество visual lines.

        Первая строка начинается с фиксированного Y.
        Последняя добавляется только если ВСЯ её высота
        помещается в рабочую область.
        """

        font = tkfont.Font(
            family=self.content_font_family,
            size=self.reader_font_size
        )

        line_height = max(
            1,
            font.metrics(
                'linespace'
            )
        )

        # Межстрочный интервал соответствует старому Text.
        line_gap = 1

        pitch = (
            line_height
            + line_gap
        )

        # Фиксированные внутренние отступы.
        top_padding = 14
        bottom_padding = 14

        usable_height = max(
            0,
            text_height
            - top_padding
            - bottom_padding
        )

        # Именно FLOOR.
        #
        # Никакая строка после этого количества физически
        # не будет нарисована.
        max_lines = max(
            1,
            (
                usable_height + line_gap
            )
            // pitch
        )

        lines = self.wrap_global_excerpt_lines(
            excerpt,
            text_width
        )

        if not lines:
            return (
                [],
                top_padding,
                line_height,
                pitch
            )

        # ---------------------------------------------
        # Находим visual line совпадения.
        # ---------------------------------------------

        match_line = 0

        for index, line in enumerate(lines):
            start = line['start']
            end = max(
                start + 1,
                line['end']
            )

            if (
                local_start < end
                and local_end > start
            ):
                match_line = index
                break

            if start <= local_start:
                match_line = index

        # Совпадение стараемся ставить в центр.
        wanted_before = (
            max_lines // 2
        )

        first = max(
            0,
            match_line - wanted_before
        )

        last = min(
            len(lines),
            first + max_lines
        )

        # Если дошли до конца excerpt,
        # заполняем свободное место строками сверху.
        first = max(
            0,
            last - max_lines
        )

        visible = lines[
            first:last
        ]

        # ---------------------------------------------
        # Финальная пиксельная проверка.
        #
        # Здесь нельзя полагаться только на max_lines:
        # каждый Y проверяется непосредственно.
        # ---------------------------------------------

        checked = []

        y = top_padding

        safe_bottom = (
            text_height
            - bottom_padding
        )

        for line in visible:
            # Нижняя граница glyph line.
            line_bottom = (
                y + line_height
            )

            if line_bottom > safe_bottom:
                break

            checked.append(
                line
            )

            y += pitch

        return (
            checked,
            top_padding,
            line_height,
            pitch
        )

    def draw_global_excerpt_canvas(
        self,
        canvas,
        excerpt,
        local_start,
        local_end
    ):
        canvas.delete('all')

        canvas.configure(
            bg=self.bg_color()
        )

        self.root.update_idletasks()

        width = max(
            1,
            canvas.winfo_width()
        )

        height = max(
            1,
            canvas.winfo_height()
        )

        left_padding = 15
        right_padding = 15

        text_width = max(
            20,
            width
            - left_padding
            - right_padding
        )

        (
            lines,
            top_padding,
            line_height,
            pitch
        ) = self.get_global_excerpt_visible_lines(
            excerpt,
            local_start,
            local_end,
            text_width,
            height
        )

        font = tkfont.Font(
            family=self.content_font_family,
            size=self.reader_font_size
        )

        y = top_padding

        marker_color = (
            self.get_search_normal_display_color()
        )

        for line_index, line in enumerate(
            lines
        ):
            line_start = line['start']
            line_end = line['end']
            value = line['text']

            # Last displayed line is not stretched.
            justify = (
                self.content_full_justify
                and line_index < len(lines) - 1
                and ' ' in value.strip()
            )

            if justify:
                pieces = list(
                    re.finditer(
                        r'\S+',
                        value
                    )
                )

                if len(pieces) > 1:
                    words_width = sum(
                        font.measure(
                            match.group(0)
                        )
                        for match
                        in pieces
                    )

                    extra = max(
                        0.0,
                        (
                            text_width
                            - words_width
                        )
                        / float(
                            len(pieces) - 1
                        )
                    )

                    x = float(
                        left_padding
                    )

                    for word_index, match in enumerate(
                        pieces
                    ):
                        word = match.group(0)

                        abs_start = (
                            line_start
                            + match.start()
                        )

                        abs_end = (
                            line_start
                            + match.end()
                        )

                        word_width = (
                            font.measure(word)
                        )

                        a = max(
                            local_start,
                            abs_start
                        )

                        b = min(
                            local_end,
                            abs_end
                        )

                        if b > a:
                            before = word[
                                :a - abs_start
                            ]

                            selected = word[
                                a - abs_start:
                                b - abs_start
                            ]

                            hx1 = (
                                x
                                + font.measure(
                                    before
                                )
                            )

                            hx2 = (
                                hx1
                                + font.measure(
                                    selected
                                )
                            )

                            canvas.create_rectangle(
                                hx1,
                                y,
                                hx2,
                                y + line_height,
                                fill=marker_color,
                                outline=''
                            )

                        canvas.create_text(
                            x,
                            y,
                            text=word,
                            font=font,
                            fill=self.text_color(),
                            anchor='nw'
                        )

                        x += word_width

                        if (
                            word_index
                            < len(pieces) - 1
                        ):
                            x += extra

                    y += pitch
                    continue

            # Normal line.
            a = max(
                local_start,
                line_start
            )

            b = min(
                local_end,
                line_end
            )

            if b > a:
                local_a = (
                    a - line_start
                )

                local_b = (
                    b - line_start
                )

                hx1 = (
                    left_padding
                    + font.measure(
                        value[:local_a]
                    )
                )

                hx2 = (
                    left_padding
                    + font.measure(
                        value[:local_b]
                    )
                )

                canvas.create_rectangle(
                    hx1,
                    y,
                    hx2,
                    y + line_height,
                    fill=marker_color,
                    outline=''
                )

            canvas.create_text(
                left_padding,
                y,
                text=value,
                font=font,
                fill=self.text_color(),
                anchor='nw'
            )

            y += pitch

    def create_global_search_result_card(
        self,
        parent,
        result,
        index
    ):
        geometry = (
            self.get_global_result_card_geometry()
        )

        title_width = geometry[
            'title_width'
        ]

        text_width = geometry[
            'text_width'
        ]

        gap = geometry[
            'gap'
        ]

        card_height = geometry[
            'height'
        ]

        cards_width = geometry[
            'total_width'
        ]

        holder = Frame(
            parent,
            bg=self.bg_color(),
            width=cards_width,
            height=card_height
        )

        holder.pack_propagate(
            False
        )

        right_x = (
            title_width
            + gap
        )

        # =====================================================
        # Border containers.
        #
        # Внешний Frame сам является рамкой:
        # внутренний content отступает ровно на 1 px.
        # =====================================================

        left_border = Frame(
            holder,
            bg=self.bg_color(),
            bd=0,
            highlightthickness=0
        )

        left_border.place(
            x=0,
            y=0,
            width=title_width,
            height=card_height
        )

        right_border = Frame(
            holder,
            bg=self.bg_color(),
            bd=0,
            highlightthickness=0
        )

        right_border.place(
            x=right_x,
            y=0,
            width=text_width,
            height=card_height
        )

        left_content = Frame(
            left_border,
            bg=self.bg_color(),
            bd=0,
            highlightthickness=0
        )

        left_content.place(
            x=1,
            y=1,
            width=max(
                1,
                title_width - 2
            ),
            height=max(
                1,
                card_height - 2
            )
        )

        right_content = Frame(
            right_border,
            bg=self.bg_color(),
            bd=0,
            highlightthickness=0
        )

        right_content.place(
            x=1,
            y=1,
            width=max(
                1,
                text_width - 2
            ),
            height=max(
                1,
                card_height - 2
            )
        )

        # =====================================================
        # Left title.
        # =====================================================

        title_label = tk.Label(
            left_content,
            text='\n'.join(
                result[
                    'title_lines'
                ]
            ),
            font=self.label_font,
            bg=self.bg_color(),
            fg=self.text_color(),
            justify=tk.LEFT,
            anchor='nw',
            wraplength=max(
                20,
                title_width - 30
            )
        )

        title_label.place(
            x=14,
            y=14,
            width=max(
                20,
                title_width - 28
            ),
            height=max(
                20,
                card_height - 28
            )
        )

        # =====================================================
        # Right excerpt.
        #
        # Теперь Canvas вместо Text.
        # Никакого внутреннего scrollbar / viewport.
        # =====================================================

        excerpt_canvas = Canvas(
            right_content,
            bg=self.bg_color(),
            bd=0,
            highlightthickness=0
        )

        excerpt_canvas.place(
            x=0,
            y=0,
            width=max(
                1,
                text_width - 2
            ),
            height=max(
                1,
                card_height - 2
            )
        )

        (
            excerpt,
            local_start,
            local_end
        ) = self.get_global_result_excerpt(
            result
        )

        # Данные сохраняем прямо в Canvas, чтобы при
        # окончательном Configure можно было нарисовать
        # строки уже по точной фактической ширине.
        excerpt_canvas._ra_excerpt = (
            excerpt
        )

        excerpt_canvas._ra_match_start = (
            local_start
        )

        excerpt_canvas._ra_match_end = (
            local_end
        )

        def redraw_excerpt(
            event=None,
            canvas=excerpt_canvas
        ):
            try:
                self.draw_global_excerpt_canvas(
                    canvas,
                    canvas._ra_excerpt,
                    canvas._ra_match_start,
                    canvas._ra_match_end
                )
            except Exception:
                pass

        excerpt_canvas.bind(
            '<Configure>',
            redraw_excerpt
        )

        widgets = [
            holder,
            left_border,
            right_border,
            left_content,
            right_content,
            title_label,
            excerpt_canvas
        ]

        for widget in widgets:
            self.bind_global_result_widget(
                widget,
                index
            )

        self.global_search_result_items.append({
            'result':
                result,

            'holder':
                holder,

            'border_frames':
                [
                    left_border,
                    right_border
                ],

            'widgets':
                widgets,

            'excerpt_canvas':
                excerpt_canvas
        })

        # После завершения layout рисуем ещё раз.
        self.root.after_idle(
            redraw_excerpt
        )

        return holder

    def render_global_search_results(
        self,
        restore_scroll=False
    ):
        if not self.global_search_content_frame:
            return

        if (
            restore_scroll
            and self.global_search_canvas
        ):
            target_yview = (
                self.global_search_saved_yview
            )
        else:
            target_yview = 0.0

        for child in (
            self.global_search_content_frame
            .winfo_children()
        ):
            try:
                child.destroy()
            except Exception:
                pass

        self.global_search_result_items = []
        self.global_search_hover_index = None

        self.root.update_idletasks()

        width = max(
            1,
            (
                self.global_search_canvas.winfo_width()
                if self.global_search_canvas
                else 1
            ),
            self.canvas.winfo_width()
        )

        geometry = (
            self.get_global_result_card_geometry()
        )

        cards_width = geometry[
            'total_width'
        ]

        card_height = geometry[
            'height'
        ]

        card_x = max(
            0,
            (
                width
                - cards_width
            ) // 2
        )

        page_results = (
            self.get_global_page_results()
        )

        if (
            len(
                self.global_search_query
            )
            >= self.SEARCH_MIN_CHARS
        ):
            for index, result in enumerate(
                page_results
            ):
                row = Frame(
                    self.global_search_content_frame,
                    bg=self.bg_color(),
                    height=(
                        card_height
                        + self.GLOBAL_RESULT_VERTICAL_GAP
                    )
                )

                row.pack(
                    fill=tk.X
                )

                row.pack_propagate(
                    False
                )

                holder = (
                    self.create_global_search_result_card(
                        row,
                        result,
                        index
                    )
                )

                holder.place(
                    x=card_x,
                    y=0,
                    width=cards_width,
                    height=card_height
                )

        # -----------------------------------------------------
        # Result paging
        # -----------------------------------------------------

        if (
            len(
                self.global_search_results
            )
            > self.GLOBAL_RESULTS_PER_PAGE
        ):
            nav = Frame(
                self.global_search_content_frame,
                bg=self.bg_color(),
                height=(
                    50
                    + self.GLOBAL_RESULTS_BOTTOM_PADDING
                )
            )

            nav.pack(
                fill=tk.X
            )

            nav.pack_propagate(
                False
            )

            center = (
                width // 2
            )

            previous_enabled = (
                self.global_search_page > 0
            )

            next_enabled = (
                self.global_search_page + 1
                < self.get_global_search_page_count()
            )

            previous_label = tk.Label(
                nav,
                bg=self.bg_color(),
                image=self.photo_frames[
                    '27'
                ][
                    10
                    if previous_enabled
                    else 5
                ],
                cursor=(
                    'hand2'
                    if previous_enabled
                    else 'arrow'
                )
            )

            previous_label.place(
                x=center - 42,
                y=10,
                width=24,
                height=24
            )

            next_label = tk.Label(
                nav,
                bg=self.bg_color(),
                image=self.photo_frames[
                    '28'
                ][
                    10
                    if next_enabled
                    else 5
                ],
                cursor=(
                    'hand2'
                    if next_enabled
                    else 'arrow'
                )
            )

            next_label.place(
                x=center + 18,
                y=10,
                width=24,
                height=24
            )

            if previous_enabled:
                previous_label.bind(
                    '<Button-1>',
                    lambda event:
                    self.global_search_previous_page()
                )

            if next_enabled:
                next_label.bind(
                    '<Button-1>',
                    lambda event:
                    self.global_search_next_page()
                )

            for widget in (
                nav,
                previous_label,
                next_label
            ):
                widget.bind(
                    '<MouseWheel>',
                    self.on_global_search_mousewheel
                )

                widget.bind(
                    '<Button-4>',
                    self.on_global_search_mousewheel
                )

                widget.bind(
                    '<Button-5>',
                    self.on_global_search_mousewheel
                )

        self.root.update_idletasks()

        if (
            self.global_search_canvas
            and self.global_search_window_item
            is not None
        ):
            try:
                actual_width = max(
                    1,
                    self.global_search_canvas.winfo_width()
                )

                self.global_search_canvas.itemconfigure(
                    self.global_search_window_item,
                    width=actual_width
                )

                self.recenter_global_search_cards()

                bbox = (
                    self.global_search_canvas.bbox(
                        'all'
                    )
                )

                if bbox:
                    self.global_search_canvas.configure(
                        scrollregion=bbox
                    )

                if (
                    self.global_search_content_frame
                    .winfo_reqheight()
                    >
                    self.global_search_canvas
                    .winfo_height()
                ):
                    local_results_top = (
                        self.GLOBAL_RESULTS_TOP
                        - self.TOP_BAR_HEIGHT
                    )

                    self.global_search_scrollbar.place(
                        relx=1.0,
                        x=-16,
                        y=local_results_top,
                        width=16,
                        height=max(
                            40,
                            self.canvas.winfo_height()
                            - local_results_top
                        )
                    )

                    self.global_search_scrollbar.lift()

                else:
                    self.global_search_scrollbar.place_forget()

                self.global_search_canvas.yview_moveto(
                    target_yview
                )

            except Exception:
                pass

    def open_global_search_result(
        self,
        index
    ):
        page_results = (
            self.get_global_page_results()
        )

        if (
            index < 0
            or index >= len(
                page_results
            )
        ):
            return 'break'

        result = (
            page_results[
                index
            ]
        )

        if self.global_search_canvas:
            try:
                view = (
                    self.global_search_canvas.yview()
                )

                if view:
                    self.global_search_return_yview = (
                        float(
                            view[0]
                        )
                    )

            except Exception:
                self.global_search_return_yview = 0.0

        self.global_search_return_page = (
            self.global_search_page
        )

        self.selected_file = (
            Path(
                result[
                    'path'
                ]
            )
        )

        self.selected_source_type = (
            result[
                'source_type'
            ]
        )

        self.reader_source_type = (
            result[
                'source_type'
            ]
        )

        self.reader_from_global_search = True

        self.suppress_reader_position_save = True

        self.global_search_target_position = (
            int(
                result[
                    'position'
                ]
            )
        )

        self.search_query = (
            self.global_search_query
        )

        self.change_screen(
            'reader'
        )

        return 'break'

    def restore_global_search_after_reader(
        self
    ):
        self.suppress_reader_position_save = (
            False
        )

        self.reader_from_global_search = (
            False
        )

        self.global_search_target_position = (
            None
        )

        self.global_search_page = (
            self.global_search_return_page
        )

        self.global_search_saved_yview = (
            self.global_search_return_yview
        )

        self.current_screen = (
            'search'
        )

        self.draw_current_screen(
            10
        )

        # Дополнительное центрирование после того,
        # как вся геометрия Tk окончательно рассчитана.
        self.root.after_idle(
            self.recenter_global_search_cards
        )

    # =========================================================
    # SEARCH POSITIONING IN READER
    # =========================================================

    def find_reader_start_for_target_line(
        self,
        target_position,
        target_line=None
    ):
        if target_line is None:
            target_line = (
                self.SEARCH_TARGET_VISUAL_LINE
            )

        if not self.reader_content:
            return 0

        target_position = max(
            0,
            min(
                int(
                    target_position
                ),
                len(
                    self.reader_content
                ) - 1
            )
        )

        # Для 7-й строки нужно найти приблизительно
        # шесть визуальных строк перед совпадением.
        wanted_previous_lines = max(
            0,
            target_line - 1
        )

        if wanted_previous_lines <= 0:
            return (
                self.normalize_slider_target(
                    target_position
                )
            )

        max_width = (
            self.get_reader_available_width()
        )

        # Берём достаточно большой фрагмент назад,
        # затем строим визуальные строки вперёд.
        chars_back = max(
            6000,
            wanted_previous_lines * 1200
        )

        chunk_start = max(
            0,
            target_position - chars_back
        )

        text = (
            self.reader_content
        )

        while (
            chunk_start > 0
            and not text[
                chunk_start - 1
            ].isspace()
        ):
            chunk_start -= 1

        position = (
            self.normalize_page_start(
                chunk_start
            )
        )

        line_starts = []

        safety = 0

        while (
            position < len(
                text
            )
            and position <= target_position
            and safety < 20000
        ):
            safety += 1

            line = (
                self.build_one_visual_line(
                    position,
                    max_width
                )
            )

            if line is None:
                break

            line_start = (
                line[
                    'start'
                ]
            )

            line_end = max(
                line[
                    'end'
                ],
                line_start + 1
            )

            if (
                line.get(
                    'text',
                    ''
                ).strip()
            ):
                line_starts.append(
                    line_start
                )

            if (
                line_start
                <= target_position
                < line_end
            ):
                break

            new_position = (
                line[
                    'end'
                ]
            )

            if new_position <= position:
                new_position = (
                    position + 1
                )

            position = (
                new_position
            )

        if not line_starts:
            return (
                self.normalize_slider_target(
                    target_position
                )
            )

        # Последняя запись — строка совпадения
        # либо ближайшая строка перед ним.
        index = max(
            0,
            len(
                line_starts
            )
            - 1
            - wanted_previous_lines
        )

        return (
            line_starts[
                index
            ]
        )

    def show_search_match_with_context(
        self,
        position
    ):
        if not self.text_widget:
            return

        start = (
            self.find_reader_start_for_target_line(
                position,
                self.SEARCH_TARGET_VISUAL_LINE
            )
        )

        self.reader_back_history = []
        self.reader_forward_history = []

        self.show_reader_page_from_position(
            start,
            silent_save=True
        )

    # =========================================================
    # TOP SEARCH GEOMETRY
    # =========================================================

    def ranges_collide(
        self,
        left_a,
        right_a,
        left_b,
        right_b,
        gap=None
    ):
        if gap is None:
            gap = (
                self.SEARCH_COLLISION_GAP
            )

        return not (
            right_a + gap <= left_b
            or
            right_b + gap <= left_a
        )

    def get_top_icon_positions(
        self,
        width
    ):
        x10 = (
            width - 20
        )

        x11 = (
            x10 - 32
        )

        x14 = (
            x11 - 96
        )

        x13 = (
            x14 - 32
        )

        x12 = (
            x13 - 32
        )

        x16 = 20
        x17 = (
            x16 + 32
        )

        x18 = (
            x17 + 96
        )

        x19 = (
            x18 + 32
        )

        return {
            '10': x10,
            '11': x11,

            '12': x12,
            '13': x13,
            '14': x14,

            '16': x16,
            '17': x17,

            '18': x18,
            '19': x19
        }

    def get_search_geometry(
        self,
        width,
        narrow=False
    ):
        center_x = (
            width // 2
        )

        if narrow:
            box_width = (
                self.SEARCH_BOX_NARROW_WIDTH
            )

            image_key = (
                '34'
            )

        else:
            box_width = (
                self.SEARCH_BOX_WIDTH
            )

            image_key = (
                '30'
            )

        left = (
            center_x
            - box_width // 2
        )

        right = (
            center_x
            + box_width // 2
        )

        half_icon = (
            self.SEARCH_ICON_SIZE
            // 2
        )

        x31 = (
            right
            + self.SEARCH_ICON_FIRST_GAP
            + half_icon
        )

        x32 = (
            x31
            + self.SEARCH_ICON_SIZE
            + self.SEARCH_ICON_GAP
        )

        x33 = (
            x32
            + self.SEARCH_ICON_SIZE
            + self.SEARCH_ICON_GAP
        )

        return {
            'image_key':
                image_key,

            'width':
                box_width,

            'center_x':
                center_x,

            'left':
                left,

            'right':
                right,

            'x31':
                x31,

            'x32':
                x32,

            'x33':
                x33,

            'left_edge':
                left,

            'right_edge':
                x33 + half_icon
        }

    def search_conflicts_with_keys(
        self,
        geometry,
        positions,
        keys
    ):
        for key in keys:
            x = (
                positions[
                    key
                ]
            )

            if self.ranges_collide(
                geometry[
                    'left_edge'
                ],
                geometry[
                    'right_edge'
                ],
                x - 12,
                x + 12
            ):
                return True

        return False

    def determine_search_layout(
        self,
        width
    ):
        positions = (
            self.get_top_icon_positions(
                width
            )
        )

        secondary = (
            '12',
            '13',
            '14',
            '18',
            '19'
        )

        primary = (
            '10',
            '11',
            '16',
            '17'
        )

        wide = (
            self.get_search_geometry(
                width,
                narrow=False
            )
        )

        wide_outside = (
            wide[
                'left_edge'
            ]
            < self.SEARCH_COLLISION_GAP

            or

            wide[
                'right_edge'
            ]
            > width
            - self.SEARCH_COLLISION_GAP
        )

        wide_collision = (
            self.search_conflicts_with_keys(
                wide,
                positions,
                secondary
            )
            or
            self.search_conflicts_with_keys(
                wide,
                positions,
                primary
            )
        )

        if (
            not wide_outside
            and not wide_collision
        ):
            return (
                'wide',
                False,
                False,
                wide
            )

        narrow = (
            self.get_search_geometry(
                width,
                narrow=True
            )
        )

        narrow_outside = (
            narrow[
                'left_edge'
            ]
            < self.SEARCH_COLLISION_GAP

            or

            narrow[
                'right_edge'
            ]
            > width
            - self.SEARCH_COLLISION_GAP
        )

        secondary_collision = (
            self.search_conflicts_with_keys(
                narrow,
                positions,
                secondary
            )
        )

        primary_collision = (
            self.search_conflicts_with_keys(
                narrow,
                positions,
                primary
            )
        )

        if (
            not narrow_outside
            and not secondary_collision
            and not primary_collision
        ):
            return (
                'narrow',
                False,
                False,
                narrow
            )

        if (
            not narrow_outside
            and not primary_collision
        ):
            return (
                'narrow',
                True,
                False,
                narrow
            )

        return (
            'narrow',
            True,
            True,
            narrow
        )

    # =========================================================
    # OVERLAY
    # =========================================================

    def add_overlay_button(
        self,
        canvas,
        key,
        x,
        y,
        command,
        enabled=True
    ):
        background = (
            canvas.create_image(
                x,
                y,
                image=self.photo_frames[
                    '15'
                ][0],
                anchor='center'
            )
        )

        alpha = (
            10
            if enabled
            else 5
        )

        icon = (
            canvas.create_image(
                x,
                y,
                image=self.photo_frames[
                    key
                ][alpha],
                anchor='center'
            )
        )

        self.overlay_buttons.append({
            'canvas':
                canvas,

            'key':
                key,

            'x':
                x,

            'y':
                y,

            'plashka':
                background,

            'icon':
                icon,

            'command':
                command,

            'enabled':
                enabled
        })

    def get_closed_search_icon_visibility(
        self,
        width
    ):
        """
        Visibility of side top icons when the centered
        20.png search icon is shown.

        First hide secondary theme/page controls.
        If still too narrow, hide primary controls too.
        """

        positions = (
            self.get_top_icon_positions(
                width
            )
        )

        center = (
            width // 2
        )

        # 20.png is 24x24. We keep a visible gap.
        search_left = (
            center - 12
        )

        search_right = (
            center + 12
        )

        secondary = (
            '12',
            '13',
            '14',
            '18',
            '19'
        )

        primary = (
            '10',
            '11',
            '16',
            '17'
        )

        secondary_collision = False

        for key in secondary:
            x = positions[
                key
            ]

            if self.ranges_collide(
                search_left,
                search_right,
                x - 12,
                x + 12,
                gap=12
            ):
                secondary_collision = True
                break

        # After secondary icons disappear, test only
        # unavoidable primary controls.
        primary_collision = False

        for key in primary:
            x = positions[
                key
            ]

            if self.ranges_collide(
                search_left,
                search_right,
                x - 12,
                x + 12,
                gap=12
            ):
                primary_collision = True
                break

        return (
            secondary_collision,
            primary_collision
        )

    def get_general_top_visibility(
        self,
        width
    ):
        """
        Collision policy for screens without an active
        search field.

        secondary = theme/page controls
        primary   = home/back + 10/11

        On reader/notes the center object is 20.png.
        On list/menu screens the center object can be Continue.

        We also prevent left and right icon groups from
        colliding with each other.
        """

        positions = self.get_top_icon_positions(
            width
        )

        hide_secondary = False
        hide_primary = False

        secondary_keys = (
            '12',
            '13',
            '14',
            '18',
            '19'
        )

        primary_keys = (
            '10',
            '11',
            '16',
            '17'
        )

        # -----------------------------------------------------
        # Center occupied area.
        # -----------------------------------------------------

        center_left = None
        center_right = None

        if self.current_screen in (
            'reader',
            'notes'
        ):
            center = (
                width // 2
            )

            center_left = center - 12
            center_right = center + 12

        elif (
            self.current_screen
            in (
                'books',
                'transmissions',
                'projects',
                'files'
            )
            and self.has_valid_continue_file()
        ):
            center = (
                width // 2
            )

            center_left = (
                center
                - self.CONTINUE_WIDTH // 2
            )

            center_right = (
                center
                + self.CONTINUE_WIDTH // 2
            )

        # -----------------------------------------------------
        # Secondary -> center collision.
        # -----------------------------------------------------

        if center_left is not None:
            for key in secondary_keys:
                x = positions[key]

                if self.ranges_collide(
                    center_left,
                    center_right,
                    x - 12,
                    x + 12,
                    gap=10
                ):
                    hide_secondary = True
                    break

        # -----------------------------------------------------
        # Side groups collide with each other.
        #
        # Nearest left-side icon is 17 or 19.
        # Nearest right-side icon is 14/12 etc.
        # -----------------------------------------------------

        visible_left = [
            positions['16'],
            positions['17']
        ]

        visible_right = [
            positions['10'],
            positions['11']
        ]

        if not hide_secondary:
            visible_left.extend([
                positions['18'],
                positions['19']
            ])

            visible_right.extend([
                positions['12'],
                positions['13'],
                positions['14']
            ])

        if (
            visible_left
            and visible_right
        ):
            left_edge = (
                max(visible_left) + 12
            )

            right_edge = (
                min(visible_right) - 12
            )

            if (
                left_edge + 12
                > right_edge
            ):
                hide_secondary = True

        # -----------------------------------------------------
        # After secondary are hidden, test primary vs center.
        # -----------------------------------------------------

        if center_left is not None:
            for key in primary_keys:
                x = positions[key]

                if self.ranges_collide(
                    center_left,
                    center_right,
                    x - 12,
                    x + 12,
                    gap=10
                ):
                    hide_primary = True
                    break

        # Even without a center item primary groups may collide
        # on a very narrow window.
        if not hide_primary:
            left_primary_right = max(
                positions['16'],
                positions['17']
            ) + 12

            right_primary_left = min(
                positions['10'],
                positions['11']
            ) - 12

            if (
                left_primary_right + 12
                > right_primary_left
            ):
                hide_primary = True

        return (
            hide_secondary,
            hide_primary
        )

    def get_settings_snapshot(self):
        return {
            'theme_name':
                self.theme_name,

            'themes':
                {
                    key: dict(value)
                    for key, value
                    in self.THEMES.items()
                },

            'markers':
                dict(
                    self.theme_marker_colors
                ),

            'font_family':
                self.content_font_family,

            'font_size':
                self.reader_font_size,

            'page_width':
                self.reader_text_max_width,

            'format':
                self.content_full_justify,

            'video_folder':
                self.video_folder,

            'audio_folder':
                self.audio_folder
        }

    def restore_settings_snapshot(self):
        data = self.settings_snapshot

        if not data:
            return

        self.theme_name = (
            data['theme_name']
        )

        for key, value in (
            data['themes'].items()
        ):
            self.THEMES[key].update(
                value
            )

        self.theme_marker_colors = dict(
            data['markers']
        )

        self.content_font_family = (
            data['font_family']
        )

        self.reader_font_size = (
            data['font_size']
        )

        self.reader_text_max_width = (
            data['page_width']
        )

        self.content_full_justify = (
            data['format']
        )

        self.video_folder = (
            data['video_folder']
        )

        self.audio_folder = (
            data['audio_folder']
        )

        self.apply_live_settings()

    def apply_live_settings(self):
        self.reader_font = (
            self.content_font_family,
            self.reader_font_size
        )

        self.reader_font_bold = (
            self.content_font_family,
            self.reader_font_size,
            'bold'
        )

        self.reader_font_italic = (
            self.content_font_family,
            self.reader_font_size,
            'italic'
        )

        self.rebuild_fade_colors()
        self.apply_theme_to_widgets()

        if self.current_screen == 'reader':
            preserve = self.reader_page_start

            if self.text_widget:
                width = (
                    self.reader_container.winfo_width()
                )

                self.text_widget.configure(
                    font=self.reader_font,
                    padx=(
                        0
                        if self.reader_two_page_mode
                        else
                        self.get_reader_side_padding(
                            width
                        )
                    )
                )

                if (
                    self.reader_two_page_mode
                    and self.second_text_widget
                ):
                    self.second_text_widget.configure(
                        font=self.reader_font,
                        padx=0
                    )

                for tag in (
                    'speaker',
                    'document_bold',
                    'title'
                ):
                    self.text_widget.tag_config(
                        tag,
                        font=self.reader_font_bold
                    )

                self.root.update_idletasks()

                self.refresh_reader_font_cache()
                self.calculate_reader_lines_per_page()
                self.clear_reader_layout_cache()

                self.show_reader_page_from_position(
                    preserve,
                    silent_save=True
                )

        elif self.current_screen == 'notes':
            if self.notes_text:
                self.notes_text.configure(
                    font=self.reader_font
                )

                self.configure_notes_tags()
                self.apply_notes_width_mode()

            self.build_overlay()

        elif self.current_screen == 'search':
            self.draw_global_search_screen(
                preserve_scroll=True
            )

            self.build_overlay()

        else:
            self.draw_current_screen(
                10
            )

    def settings_choose_color(
        self,
        kind
    ):
        theme = (
            self.theme_name
        )

        if kind == 'background':
            current = self.THEMES[
                theme
            ]['background']

        elif kind == 'text':
            current = self.THEMES[
                theme
            ]['text']

        else:
            current = self.theme_marker_colors[
                theme
            ]

        value = colorchooser.askcolor(
            color=current,
            parent=self.settings_window
        )

        if not value or not value[1]:
            return

        color = value[1]

        if kind == 'marker':
            self.theme_marker_colors[
                theme
            ] = color
        else:
            self.THEMES[
                theme
            ][kind] = color

        self.draw_settings_color_squares()
        self.apply_live_settings()

    def draw_settings_color_squares(self):
        if not self.settings_canvas:
            return

        values = (
            self.THEMES[
                self.theme_name
            ]['background'],

            self.THEMES[
                self.theme_name
            ]['text'],

            self.theme_marker_colors[
                self.theme_name
            ]
        )

        for key, value in zip(
            (
                'background',
                'text',
                'marker'
            ),
            values
        ):
            item = self.settings_color_items.get(
                key
            )

            if item is not None:
                self.settings_canvas.itemconfig(
                    item,
                    fill=value
                )

    def settings_set_theme(
        self,
        value
    ):
        if value not in self.THEMES:
            return

        self.theme_name = value

        x = {
            'day': 45,
            'sepia': 77,
            'night': 109
        }[value]

        if self.settings_theme_underline:
            self.settings_canvas.coords(
                self.settings_theme_underline,
                x,
                51
            )

        self.draw_settings_color_squares()
        self.apply_live_settings()

    def settings_change_font_size(
        self,
        delta
    ):
        try:
            value = int(
                self.settings_font_size_var.get()
            )
        except Exception:
            value = self.reader_font_size

        value = max(
            8,
            min(
                100,
                value + delta
            )
        )

        self.reader_font_size = value

        self.settings_font_size_var.set(
            str(value)
        )

        self.apply_live_settings()

    def settings_change_page_width(
        self,
        delta
    ):
        try:
            value = int(
                self.settings_page_width_var.get()
            )
        except Exception:
            value = self.reader_text_max_width

        value = max(
            300,
            min(
                5000,
                value + delta
            )
        )

        self.reader_text_max_width = value

        self.settings_page_width_var.set(
            str(value)
        )

        self.apply_live_settings()

    def settings_font_selected(
        self,
        event=None
    ):
        value = self.settings_font_combo.get()

        if value:
            self.content_font_family = value
            self.apply_live_settings()

    def settings_toggle_format(self):
        self.content_full_justify = (
            not self.content_full_justify
        )

        key = (
            '44'
            if self.content_full_justify
            else '43'
        )

        if (
            self.settings_canvas
            and self.settings_format_item
        ):
            self.settings_canvas.itemconfig(
                self.settings_format_item,
                image=self.photo_frames[
                    key
                ][10]
            )

        # Clear reader layout so 43/44 is immediately
        # reconstructed, rather than using cached pages.
        if self.current_screen == 'reader':
            self.clear_reader_layout_cache()

        self.apply_live_settings()

    def settings_choose_folder(
        self,
        kind
    ):
        current = (
            self.video_folder
            if kind == 'video'
            else self.audio_folder
        )

        value = filedialog.askdirectory(
            parent=self.settings_window,
            initialdir=(
                current
                if current
                and Path(current).exists()
                else str(self.base_dir)
            )
        )

        if not value:
            return

        if kind == 'video':
            self.video_folder = value
        else:
            self.audio_folder = value

    def cancel_settings_window(self):
        if not self.settings_window:
            return

        self.restore_settings_snapshot()

        self.settings_preview_active = False

        try:
            self.settings_window.destroy()
        except Exception:
            pass

        self.settings_window = None
        self.settings_canvas = None
        self.settings_snapshot = None

    def accept_settings_window(self):
        if not self.settings_window:
            return

        self.settings_preview_active = False

        self.save_settings()

        try:
            self.settings_window.destroy()
        except Exception:
            pass

        self.settings_window = None
        self.settings_canvas = None
        self.settings_snapshot = None

    def open_settings_window(self):
        if self.settings_window:
            try:
                self.settings_window.lift()
                self.settings_window.focus_force()
                return
            except Exception:
                self.settings_window = None

        self.settings_snapshot = (
            self.get_settings_snapshot()
        )

        self.settings_preview_active = True

        window = tk.Toplevel(
            self.root
        )

        self.settings_window = window

        window.title(
            'Настройки'
        )

        window.resizable(
            False,
            False
        )

        window.attributes(
            '-topmost',
            True
        )

        width = 540
        height = 212

        screen_width = (
            window.winfo_screenwidth()
        )

        screen_height = (
            window.winfo_screenheight()
        )

        x = (
            screen_width - width
        ) // 2

        y = (
            screen_height - height
        ) // 2

        window.geometry(
            f'{width}x{height}+{x}+{y}'
        )

        bg = '#e3e4c9'

        canvas = Canvas(
            window,
            width=width,
            height=height,
            bg=bg,
            highlightthickness=0,
            bd=0
        )

        canvas.pack(
            fill=tk.BOTH,
            expand=True
        )

        self.settings_canvas = (
            canvas
        )

        font = (
            'Alice',
            15
        )

        def label(
            x,
            y,
            value
        ):
            canvas.create_text(
                x,
                y,
                text=value,
                font=font,
                fill='#000000',
                anchor='w'
            )

        # ---------------------------------------------
        # Theme 14/13/12
        # ---------------------------------------------

        for theme, key, x in (
            ('day', '14', 45),
            ('sepia', '13', 77),
            ('night', '12', 109)
        ):
            item = canvas.create_image(
                x,
                38,
                image=self.photo_frames[
                    key
                ][10],
                anchor='center'
            )

            canvas.tag_bind(
                item,
                '<Button-1>',
                lambda event,
                value=theme:
                self.settings_set_theme(
                    value
                )
            )

        underline_x = {
            'day': 45,
            'sepia': 77,
            'night': 109
        }.get(
            self.theme_name,
            77
        )

        self.settings_theme_underline = (
            canvas.create_image(
                underline_x,
                51,
                image=self.photo_frames[
                    '26'
                ][10],
                anchor='center'
            )
        )

        # ---------------------------------------------
        # Colors
        # ---------------------------------------------

        color_data = (
            (
                'background',
                136,
                'Фон',
                165
            ),
            (
                'text',
                223,
                'Текст',
                252
            ),
            (
                'marker',
                326,
                'Маркер',
                355
            )
        )

        self.settings_color_items = {}

        for (
            kind,
            square_x,
            text_value,
            text_x
        ) in color_data:

            canvas.create_rectangle(
                square_x,
                28,
                square_x + 20,
                48,
                fill='#000000',
                outline=''
            )

            if kind == 'marker':
                color = self.theme_marker_colors[
                    self.theme_name
                ]
            else:
                color = self.THEMES[
                    self.theme_name
                ][kind]

            inner = canvas.create_rectangle(
                square_x + 2,
                30,
                square_x + 18,
                46,
                fill=color,
                outline=''
            )

            self.settings_color_items[
                kind
            ] = inner

            for item in (
                inner,
            ):
                canvas.tag_bind(
                    item,
                    '<Button-1>',
                    lambda event,
                    value=kind:
                    self.settings_choose_color(
                        value
                    )
                )

            label(
                text_x,
                38,
                text_value
            )

        # ---------------------------------------------
        # Folders
        # ---------------------------------------------

        video = canvas.create_image(
            463,
            38,
            image=self.photo_frames[
                '45'
            ][10],
            anchor='center'
        )

        audio = canvas.create_image(
            495,
            38,
            image=self.photo_frames[
                '46'
            ][10],
            anchor='center'
        )

        canvas.tag_bind(
            video,
            '<Button-1>',
            lambda event:
            self.settings_choose_folder(
                'video'
            )
        )

        canvas.tag_bind(
            audio,
            '<Button-1>',
            lambda event:
            self.settings_choose_folder(
                'audio'
            )
        )

        # ---------------------------------------------
        # Font
        # ---------------------------------------------

        label(
            35,
            78,
            'Шрифт'
        )

        fonts = sorted(
            set(
                tkfont.families(
                    self.root
                )
            ),
            key=str.casefold
        )

        if self.content_font_family not in fonts:
            fonts.insert(
                0,
                self.content_font_family
            )

        combo = ttk.Combobox(
            window,
            values=fonts,
            state='readonly'
        )

        combo.set(
            self.content_font_family
        )

        combo.place(
            x=125,
            y=67,
            width=179,
            height=24
        )

        combo.bind(
            '<<ComboboxSelected>>',
            self.settings_font_selected
        )

        self.settings_font_combo = (
            combo
        )

        label(
            332,
            78,
            'Размер'
        )

        minus = canvas.create_image(
            427,
            78,
            image=self.photo_frames[
                '42'
            ][10],
            anchor='center'
        )

        plus = canvas.create_image(
            494,
            78,
            image=self.photo_frames[
                '37'
            ][10],
            anchor='center'
        )

        self.settings_font_size_var = (
            tk.StringVar(
                value=str(
                    self.reader_font_size
                )
            )
        )

        size_entry = tk.Entry(
            window,
            textvariable=self.settings_font_size_var,
            font=('Alice', 13),
            justify='center',
            bd=1,
            relief=tk.SOLID
        )

        size_entry.place(
            x=443,
            y=66,
            width=35,
            height=25
        )

        canvas.tag_bind(
            minus,
            '<Button-1>',
            lambda event:
            self.settings_change_font_size(
                -1
            )
        )

        canvas.tag_bind(
            plus,
            '<Button-1>',
            lambda event:
            self.settings_change_font_size(
                1
            )
        )

        # ---------------------------------------------
        # Page width
        # ---------------------------------------------

        label(
            35,
            118,
            'Ширина страницы'
        )

        minus_width = canvas.create_image(
            257,
            118,
            image=self.photo_frames[
                '42'
            ][10],
            anchor='center'
        )

        plus_width = canvas.create_image(
            344,
            118,
            image=self.photo_frames[
                '37'
            ][10],
            anchor='center'
        )

        self.settings_page_width_var = (
            tk.StringVar(
                value=str(
                    self.reader_text_max_width
                )
            )
        )

        width_entry = tk.Entry(
            window,
            textvariable=self.settings_page_width_var,
            font=('Alice', 13),
            justify='center',
            bd=1,
            relief=tk.SOLID
        )

        width_entry.place(
            x=273,
            y=106,
            width=54,
            height=25
        )

        canvas.tag_bind(
            minus_width,
            '<Button-1>',
            lambda event:
            self.settings_change_page_width(
                -50
            )
        )

        canvas.tag_bind(
            plus_width,
            '<Button-1>',
            lambda event:
            self.settings_change_page_width(
                50
            )
        )

        # ---------------------------------------------
        # Format
        # ---------------------------------------------

        label(
            392,
            118,
            'Формат'
        )

        format_key = (
            '44'
            if self.content_full_justify
            else '43'
        )

        self.settings_format_item = (
            canvas.create_image(
                494,
                118,
                image=self.photo_frames[
                    format_key
                ][10],
                anchor='center'
            )
        )

        canvas.tag_bind(
            self.settings_format_item,
            '<Button-1>',
            lambda event:
            self.settings_toggle_format()
        )

        # ---------------------------------------------
        # Cancel / OK
        # ---------------------------------------------

        for (
            x1,
            x2,
            caption,
            command
        ) in (
            (
                33,
                253,
                'Отмена',
                self.cancel_settings_window
            ),
            (
                287,
                507,
                'ОК',
                self.accept_settings_window
            )
        ):
            rectangle = canvas.create_rectangle(
                x1,
                151,
                x2,
                187,
                fill='#c9c9ac',
                outline=''
            )

            text_item = canvas.create_text(
                (
                    x1 + x2
                ) // 2,
                169,
                text=caption,
                font=('Alice', 15),
                fill='#000000',
                anchor='center'
            )

            for item in (
                rectangle,
                text_item
            ):
                canvas.tag_bind(
                    item,
                    '<Button-1>',
                    lambda event,
                    cmd=command:
                    cmd()
                )

        window.protocol(
            'WM_DELETE_WINDOW',
            self.cancel_settings_window
        )

        window.bind(
            '<Escape>',
            lambda event:
            self.cancel_settings_window()
        )

        window.lift()
        window.focus_force()

    # =========================================================
    # HELP / ABOUT
    # =========================================================

    def close_help_window(self):
        window = self.help_window

        self.help_window = None
        self.help_canvas = None
        self.help_content = None
        self.help_canvas_window = None
        self.help_image_refs = []

        if window:
            try:
                window.destroy()
            except Exception:
                pass

    def on_help_mousewheel(
        self,
        event
    ):
        if not self.help_canvas:
            return 'break'

        try:
            if (
                getattr(
                    event,
                    'num',
                    None
                ) == 5
                or getattr(
                    event,
                    'delta',
                    0
                ) < 0
            ):
                self.help_canvas.yview_scroll(
                    3,
                    'units'
                )

            elif (
                getattr(
                    event,
                    'num',
                    None
                ) == 4
                or getattr(
                    event,
                    'delta',
                    0
                ) > 0
            ):
                self.help_canvas.yview_scroll(
                    -3,
                    'units'
                )

        except Exception:
            pass

        return 'break'

    def open_help_window(self):
        if self.help_window:
            try:
                self.help_window.deiconify()
                self.help_window.lift()
                self.help_window.focus_force()
                return
            except Exception:
                self.help_window = None

        window = tk.Toplevel(
            self.root
        )

        self.help_window = window

        window.title(
            'Ra_Reader — Справка'
        )

        window.geometry(
            '1000x760'
        )

        window.minsize(
            650,
            500
        )

        # Справка специально остаётся в спокойной сепии,
        # независимо от темы самой читалки.
        bg = '#e3e4c9'
        text_color = '#2d2d2d'
        secondary = '#626253'
        line_color = '#bfc0aa'

        window.configure(
            bg=bg
        )

        outer = Frame(
            window,
            bg=bg
        )

        outer.pack(
            fill=tk.BOTH,
            expand=True
        )

        canvas = Canvas(
            outer,
            bg=bg,
            highlightthickness=0,
            bd=0
        )

        scrollbar = Scrollbar(
            outer,
            orient=tk.VERTICAL,
            command=canvas.yview
        )

        canvas.configure(
            yscrollcommand=(
                scrollbar.set
            )
        )

        scrollbar.pack(
            side=tk.RIGHT,
            fill=tk.Y
        )

        canvas.pack(
            side=tk.LEFT,
            fill=tk.BOTH,
            expand=True
        )

        content = Frame(
            canvas,
            bg=bg
        )

        canvas_window = (
            canvas.create_window(
                0,
                0,
                window=content,
                anchor='nw'
            )
        )

        self.help_canvas = canvas
        self.help_content = content
        self.help_canvas_window = canvas_window
        self.help_image_refs = []

        wrapped_labels = []

        def update_scrollregion(
            event=None
        ):
            try:
                bbox = canvas.bbox(
                    'all'
                )

                if bbox:
                    canvas.configure(
                        scrollregion=bbox
                    )
            except Exception:
                pass

        def resize_content(
            event
        ):
            try:
                canvas.itemconfigure(
                    canvas_window,
                    width=event.width
                )

                wrap = min(
                    900,
                    max(
                        300,
                        event.width - 100
                    )
                )

                for label in wrapped_labels:
                    try:
                        label.configure(
                            wraplength=wrap
                        )
                    except Exception:
                        pass

            except Exception:
                pass

        content.bind(
            '<Configure>',
            update_scrollregion
        )

        canvas.bind(
            '<Configure>',
            resize_content
        )

        for widget in (
            window,
            canvas,
            content
        ):
            widget.bind(
                '<MouseWheel>',
                self.on_help_mousewheel
            )

            widget.bind(
                '<Button-4>',
                self.on_help_mousewheel
            )

            widget.bind(
                '<Button-5>',
                self.on_help_mousewheel
            )

        def add_label(
            value,
            font,
            color=text_color,
            pady=(0, 0),
            indent=0
        ):
            label = tk.Label(
                content,
                text=value,
                font=font,
                fg=color,
                bg=bg,
                justify=tk.LEFT,
                anchor='w'
            )

            label.pack(
                fill=tk.X,
                padx=(
                    50 + indent,
                    50
                ),
                pady=pady
            )

            wrapped_labels.append(
                label
            )

            return label

        def paragraph(
            value
        ):
            return add_label(
                value,
                (
                    'Alice',
                    13
                ),
                pady=(
                    1,
                    7
                )
            )

        def soft(
            value
        ):
            return add_label(
                value,
                (
                    'Alice',
                    13,
                    'italic'
                ),
                secondary,
                pady=(
                    3,
                    9
                )
            )

        def bullet(
            value
        ):
            return add_label(
                '• ' + value,
                (
                    'Alice',
                    13
                ),
                pady=(
                    1,
                    1
                ),
                indent=14
            )

        def heading(
            value,
            icon=None
        ):
            row = Frame(
                content,
                bg=bg
            )

            row.pack(
                fill=tk.X,
                padx=50,
                pady=(
                    20,
                    8
                )
            )

            if (
                icon
                and icon in self.images
            ):
                try:
                    photo = self.photo_frames[
                        icon
                    ][10]

                    self.help_image_refs.append(
                        photo
                    )

                    icon_label = tk.Label(
                        row,
                        image=photo,
                        bg=bg
                    )

                    icon_label.pack(
                        side=tk.LEFT,
                        padx=(
                            0,
                            12
                        )
                    )

                    icon_label.bind(
                        '<MouseWheel>',
                        self.on_help_mousewheel
                    )

                except Exception:
                    pass

            label = tk.Label(
                row,
                text=value,
                font=(
                    'Alice',
                    17,
                    'bold'
                ),
                fg=text_color,
                bg=bg,
                anchor='w'
            )

            label.pack(
                side=tk.LEFT
            )

            label.bind(
                '<MouseWheel>',
                self.on_help_mousewheel
            )

        def shortcut(
            keys,
            description
        ):
            row = Frame(
                content,
                bg=bg
            )

            row.pack(
                fill=tk.X,
                padx=64,
                pady=2
            )

            key_label = tk.Label(
                row,
                text=keys,
                font=(
                    'Consolas',
                    10,
                    'bold'
                ),
                fg=text_color,
                bg='#c9c9ac',
                padx=7,
                pady=3
            )

            key_label.pack(
                side=tk.LEFT,
                anchor='n'
            )

            description_label = tk.Label(
                row,
                text=description,
                font=(
                    'Alice',
                    13
                ),
                fg=text_color,
                bg=bg,
                justify=tk.LEFT,
                anchor='w'
            )

            description_label.pack(
                side=tk.LEFT,
                fill=tk.X,
                expand=True,
                padx=(
                    12,
                    0
                )
            )

            for item in (
                row,
                key_label,
                description_label
            ):
                item.bind(
                    '<MouseWheel>',
                    self.on_help_mousewheel
                )

        # -----------------------------------------------------
        # Header
        # -----------------------------------------------------

        header = Frame(
            content,
            bg=bg
        )

        header.pack(
            fill=tk.X,
            padx=50,
            pady=(
                38,
                0
            )
        )

        try:
            photo = self.photo_frames[
                '10'
            ][10]

            self.help_image_refs.append(
                photo
            )

            tk.Label(
                header,
                image=photo,
                bg=bg
            ).pack(
                side=tk.LEFT,
                padx=(
                    0,
                    14
                )
            )
        except Exception:
            pass

        tk.Label(
            header,
            text='Ra_Reader',
            font=(
                'Alice',
                28,
                'bold'
            ),
            fg=text_color,
            bg=bg
        ).pack(
            side=tk.LEFT
        )

        add_label(
            'Справка и немного о программе',
            (
                'Alice',
                15
            ),
            secondary,
            pady=(
                4,
                14
            )
        )

        paragraph(
            'Если по-простому — это читалка, в которой можно держать книги, передачи, '
            'проекты, свои файлы и заметки в одном месте. Она запоминает, где ты остановился, '
            'умеет искать по всей библиотеке, ставить закладки и заливки, а для передач ещё '
            'может открыть видео или аудио сразу на нужном моменте.'
        )

        soft(
            'То есть смысл программы не только в том, чтобы показать текст. '
            'Она старается запомнить всё вокруг чтения, чтобы потом не искать это заново.'
        )

        heading(
            'Что находится на главном экране'
        )

        paragraph(
            'После запуска есть три основных направления:'
        )

        bullet(
            'Поиск — ищет сразу по книгам, передачам, проектам и добавленным файлам;'
        )
        bullet(
            'Чтение — вся библиотека и документы;'
        )
        bullet(
            'Заметки — встроенный блокнот.'
        )

        heading(
            'Чтение',
            '05'
        )

        paragraph(
            'В разделе чтения всё разбито на четыре группы:'
        )

        bullet(
            'Книги — FB2 из папки книг;'
        )
        bullet(
            'Передачи — текстовые расшифровки с таймкодами;'
        )
        bullet(
            'Проекты — отдельная подборка материалов;'
        )
        bullet(
            'Файлы — свои TXT, FB2, Markdown и HTML.'
        )

        paragraph(
            'Если документ уже открывался, программа запоминает позицию. Поэтому можно '
            'закрыть её посреди книги, а потом продолжить примерно с того же места.'
        )

        paragraph(
            'Кнопка «Продолжить чтение» возвращает к последнему документу именно в том '
            'разделе, в котором ты сейчас находишься.'
        )

        heading(
            'Как листать текст',
            '18'
        )

        paragraph(
            'Читалка работает не как обычное длинное полотно, а страницами. Размер страницы '
            'рассчитывается под текущее окно, шрифт и ширину текста.'
        )

        bullet(
            'колесо мыши вверх/вниз — предыдущая или следующая страница;'
        )
        bullet(
            'Page Up / Page Down — то же самое;'
        )
        bullet(
            'кнопки со стрелками сверху — листание страниц;'
        )
        bullet(
            'ползунок снизу — быстрый переход по всему документу.'
        )

        paragraph(
            'Справа внизу показывается процент прочитанного. Для передач слева дополнительно '
            'виден текущий таймкод.'
        )

        heading(
            'Шрифт и ширина текста',
            '41'
        )

        paragraph(
            'Кнопка ширины переключает компактную колонку по центру и расширенный режим. '
            'Размер текста можно менять прямо во время чтения и в заметках.'
        )

        shortcut(
            '+',
            'увеличить размер шрифта'
        )

        shortcut(
            '−',
            'уменьшить размер шрифта'
        )

        shortcut(
            'Ctrl + колесо',
            'увеличить или уменьшить шрифт в режиме чтения и в заметках'
        )

        soft(
            'Обычное колесо без Ctrl продолжает листать страницы в читалке и прокручивать '
            'текст в заметках.'
        )

        heading(
            'Закладки',
            '21'
        )

        paragraph(
            'Закладка ставится на текущую страницу. Все закладки документа показываются '
            'маленькими маркерами прямо на нижней шкале.'
        )

        bullet(
            'кнопка закладки — поставить или убрать закладку;'
        )
        bullet(
            'стрелки рядом — перейти к предыдущей или следующей закладке;'
        )
        bullet(
            'правый клик по маркеру — удалить конкретную закладку;'
        )
        bullet(
            'правый клик по кнопке закладок — удалить все закладки документа.'
        )

        heading(
            'Заливки и выделения',
            '29'
        )

        paragraph(
            'Можно выделить кусок текста мышкой и сохранить его как цветную заливку. '
            'Она останется после закрытия программы и снова появится при открытии файла.'
        )

        bullet(
            'выдели текст и нажми кнопку заливки — фрагмент сохранится;'
        )
        bullet(
            'если весь выбранный кусок уже залит, эта же кнопка снимет заливку;'
        )
        bullet(
            'правый клик по кнопке заливки — удалить все заливки документа.'
        )

        heading(
            'Поиск внутри документа',
            '20'
        )

        paragraph(
            'Кнопка поиска сверху открывает строку поиска прямо в режиме чтения. '
            'Найденные места подсвечиваются, а текущее совпадение выделяется отдельно.'
        )

        bullet(
            'минимальная длина запроса — 2 символа;'
        )
        bullet(
            'Enter — следующее совпадение;'
        )
        bullet(
            'Shift + Enter — предыдущее;'
        )
        bullet(
            'на нижней шкале видны маркеры всех найденных мест.'
        )

        heading(
            'Глобальный поиск',
            '01'
        )

        paragraph(
            'Глобальный поиск смотрит сразу по всей библиотеке. Можно отдельно включать '
            'или выключать книги, передачи, проекты и добавленные файлы.'
        )

        paragraph(
            'Если нажать на найденный фрагмент, откроется сам документ примерно в нужном месте. '
            'Назад можно вернуться в тот же список результатов и примерно на ту же позицию прокрутки.'
        )

        heading(
            'Немного про язык поиска'
        )

        paragraph(
            'Обычный запрос просто ищет текст. Но есть ещё несколько полезных вариантов.'
        )

        soft(
            'любовь OR дружба — подходит один вариант или другой.'
        )

        soft(
            'птиц камень =5 — слова должны находиться рядом, максимум через пять слов.'
        )

        paragraph(
            'В поиске с = обычное слово может иметь продолжение. Поэтому «птиц» найдёт '
            '«птиц», «птицы», «птицами» и другие слова с таким началом.'
        )

        soft(
            '!птиц — точное слово. «птицы» в такой результат уже не попадёт.'
        )

        heading(
            'Передачи и таймкоды',
            '06'
        )

        paragraph(
            'У передач есть дополнительная возможность. В исходном TXT могут быть таймкоды, '
            'и Ra_Reader связывает их с текстом.'
        )

        paragraph(
            'Левый клик по тексту определяет ближайший подходящий таймкод выше выбранного места. '
            'Текущее время сразу показывается внизу.'
        )

        paragraph(
            'Если нажать правой кнопкой мыши по тексту передачи и ничего при этом не выделено, '
            'программа тоже определит таймкод и откроет специальное медиа-меню.'
        )

        bullet(
            'Открыть Видео — найти подходящий видеофайл и открыть его на этом моменте;'
        )
        bullet(
            'Открыть Аудио — то же самое для аудио;'
        )
        bullet(
            'Указать файл — выбрать конкретный медиафайл вручную.'
        )

        soft(
            '«Указать файл» запоминает последний использованный каталог, поэтому следующий '
            'выбор сразу начинается в той же папке.'
        )

        heading(
            'Как Ra_Reader ищет видео и аудио',
            '45'
        )

        paragraph(
            'Имена текстового файла и записи не обязаны совпадать один в один. Программа '
            'сравнивает слова, дату, похожесть названия и учитывает разные разделители и транслитерацию.'
        )

        soft(
            '2023-10-22 - Родители и дети.txt\n'
            '207. Родители и Дети (22.10.2023).mp4'
        )

        soft(
            '2023-06-29 - Магия управление силой.txt\n'
            '174_Магия_—_управление_Силой_29_06_2023.mp4'
        )

        heading(
            'MPC-HC и открытие на нужном времени'
        )

        paragraph(
            'Для MPC-HC передача таймкода поддерживается напрямую. Если в Ra_Reader выбран, '
            'например, момент 00:27:17, плееру передаётся именно 00:27:17 и запись открывается '
            'с соответствующего места.'
        )

        soft(
            'С MPC-HC этот режим проверен: таймкод передаётся в понятном самому плееру формате HH:MM:SS.'
        )

        paragraph(
            'Для других известных плееров используются их собственные способы запуска. '
            'Если конкретный плеер неизвестен, Windows всё равно может открыть файл обычной '
            'программой по умолчанию, но универсального способа передать время абсолютно любому '
            'плееру у Windows нет.'
        )

        heading(
            'Заметки',
            '03'
        )

        paragraph(
            'Заметки — это встроенный блокнот. Можно держать до десяти отдельных листов '
            'и переключаться между ними вкладками снизу.'
        )

        bullet(
            'добавлять, переименовывать и удалять листы;'
        )
        bullet(
            'перетаскивать вкладки мышкой и менять их порядок;'
        )
        bullet(
            'делать текст жирным;'
        )
        bullet(
            'делать цветные заливки;'
        )
        bullet(
            'искать внутри текущей заметки.'
        )

        paragraph(
            'Заметки сохраняются автоматически. Их ширину тоже можно переключать отдельной кнопкой.'
        )

        heading(
            'Перенести кусок книги в заметки'
        )

        paragraph(
            'В режиме чтения выдели нужный фрагмент и нажми правую кнопку мыши. '
            'Пункт «Перенести в заметки» добавит его в текущий лист.'
        )

        paragraph(
            'Если часть исходного текста была жирной, Ra_Reader старается сохранить '
            'это форматирование и в заметке.'
        )

        heading(
            'Копирование текста'
        )

        shortcut(
            'Ctrl + C',
            'обычное копирование выделенного текста'
        )

        shortcut(
            'Ctrl + W',
            'копирование с форматированием для Word / HTML'
        )

        shortcut(
            'Ctrl + M',
            'копирование с форматированием в Markdown'
        )

        paragraph(
            'При форматированном копировании учитывается жирный текст и сохранённые цветные заливки.'
        )

        heading(
            'Горячие клавиши в заметках',
            '40'
        )

        shortcut(
            'Ctrl + A',
            'выделить весь текст заметки'
        )
        shortcut(
            'Ctrl + C',
            'копировать'
        )
        shortcut(
            'Ctrl + X',
            'вырезать'
        )
        shortcut(
            'Ctrl + V',
            'вставить'
        )
        shortcut(
            'Ctrl + W',
            'копировать выделение для Word / HTML'
        )
        shortcut(
            'Ctrl + M',
            'копировать выделение как Markdown'
        )
        shortcut(
            '+ / −',
            'изменить общий размер шрифта'
        )
        shortcut(
            'Ctrl + колесо',
            'изменить общий размер шрифта'
        )

        heading(
            'Темы и настройки',
            '11'
        )

        paragraph(
            'Есть дневная, сепийная и ночная темы. Для каждой можно отдельно настроить '
            'фон, цвет текста и цвет маркера.'
        )

        paragraph(
            'В настройках также можно выбрать шрифт, размер текста, максимальную ширину страницы, '
            'выравнивание по ширине и папки с видео и аудио.'
        )

        paragraph(
            'Правый клик по кнопке настроек открывает полный сброс. Он возвращает исходное '
            'оформление и очищает сохранённые данные программы, включая заметки.'
        )

        heading(
            'Какие файлы можно добавлять',
            '36'
        )

        bullet('TXT')
        bullet('FB2')
        bullet('Markdown / MD')
        bullet('HTML / HTM')

        paragraph(
            'Добавленные вручную документы появляются в разделе «Файлы» и тоже участвуют '
            'в глобальном поиске, если для них поиск не отключён.'
        )

        heading(
            'Что программа запоминает'
        )

        bullet(
            'позицию чтения для каждого документа;'
        )
        bullet(
            'закладки и заливки;'
        )
        bullet(
            'последние открытые документы;'
        )
        bullet(
            'добавленные внешние файлы;'
        )
        bullet(
            'заметки и их форматирование;'
        )
        bullet(
            'темы, шрифт и ширину страницы;'
        )
        bullet(
            'параметры глобального поиска;'
        )
        bullet(
            'папки видео и аудио;'
        )
        bullet(
            'последнюю папку ручного выбора медиафайла;'
        )
        bullet(
            'размер и положение окна.'
        )

        heading(
            'Навигация'
        )

        shortcut(
            'Esc',
            'закрыть активный поиск или вернуться на предыдущий экран'
        )

        shortcut(
            'Page Up / Page Down',
            'предыдущая / следующая страница в режиме чтения'
        )

        paragraph(
            'Если документ открыт из глобального поиска, Esc возвращает именно к результатам '
            'этого поиска. Кнопка с домиком возвращает сразу на главный экран.'
        )

        separator = Frame(
            content,
            bg=line_color,
            height=1
        )

        separator.pack(
            fill=tk.X,
            padx=50,
            pady=(
                24,
                4
            )
        )

        heading(
            'Двухстраничный режим'
        )

        paragraph(
            'В режиме чтения клавиша 2 переключает обычный вид и разворот из двух страниц. '
            'Слева остаётся текущая страница, справа сразу показывается следующая, а между ними '
            'оставляется свободное пространство около 100 пикселей.'
        )

        shortcut(
            '2',
            'включить или выключить двухстраничный режим'
        )

        heading(
            'Сохранить выделенный текст в PNG'
        )

        paragraph(
            'В читалке и в заметках выделенный текст можно сохранить отдельной PNG-картинкой. '
            'Это не снимок экрана: текст заново формируется для изображения шириной 1000 пикселей, '
            'с текущим шрифтом, его размером, фоном и режимом выравнивания.'
        )

        paragraph(
            'Пункт «Сохранить в PNG» находится в контекстном меню выделенного текста. '
            'После выбора указывается папка и имя файла. По умолчанию предлагается Screen_001, '
            'Screen_002 и так далее, чтобы случайно не затереть предыдущую картинку.'
        )

        heading(
            'HTML, картинки и MHTML'
        )

        paragraph(
            'При добавлении HTML Ra_Reader теперь старается найти связанную с ним папку ресурсов '
            'с похожим названием и вставить картинки в те места текста, где они находятся в HTML.'
        )

        paragraph(
            'Поддерживаются также MHTML и MHT. Это удобно, когда веб-страница сохранена одним файлом: '
            'текст и встроенные изображения читаются непосредственно из этого файла. Подписи под рисунками отображаются наклонным шрифтом.'
        )

        heading(
            'Добавление своих файлов'
        )

        paragraph(
            'Через «Добавить файл» теперь можно выбрать сразу несколько документов. '
            'Подходит обычное групповое выделение мышкой, Shift или Ctrl в стандартном окне Windows.'
        )

        heading(
            'Ещё немного про поиск'
        )

        paragraph(
            'Поиск начинается уже с двух символов. В глобальном поиске после ввода текста есть '
            'небольшая задержка около двух секунд: пока ты печатаешь, таймер каждый раз запускается '
            'заново, и поиск начинается после того, как ввод остановился.'
        )

        soft(
            'Например, Аллат и !Аллат — это не одно и то же. Обычный вариант входит '
            'в более длинное слово АллатРа в поддерживаемых режимах поиска, а !Аллат требует точного слова. '
            'Поэтому количество результатов у этих двух запросов будет отличаться.'
        )

        heading(
            'Удаление добавленных файлов'
        )

        paragraph(
            'В разделе «Файлы» документ можно удалить через правую кнопку мыши. '
            'При этом он убирается не только из списка: Ra_Reader также удаляет его '
            'из поискового кэша, позиции чтения, закладок и сохранённых заливок.'
        )

        paragraph(
            'Правый клик в разделе «Файлы» также даёт команду «Очистить весь список». '
            'Она одним действием убирает все добавленные вручную документы и связанные '
            'с ними данные программы. Сами файлы на диске при этом не удаляются.'
        )

        heading(
            'Загрузка больших HTML и MHTML'
        )

        paragraph(
            'При первом открытии большой сохранённой веб-страницы программе может понадобиться '
            'немного времени на разбор текста и изображений. В этот момент внизу Reader показывается '
            'индикатор загрузки с процентами.'
        )

        paragraph(
            'После успешного разбора подготовленная версия документа остаётся в оперативной памяти. '
            'Поэтому повторное открытие того же неизменённого HTML или MHTML в течение текущего '
            'запуска Ra_Reader должно быть значительно быстрее.'
        )

        heading(
            'Если совсем коротко'
        )

        paragraph(
            'Ra_Reader — это читалка, поиск по библиотеке, заметки и связь текстовых передач '
            'с видео и аудио в одном окне. Можно просто читать, а можно поставить закладки, '
            'выделять важное, искать сразу по сотням материалов и из расшифровки передачи '
            'переходить прямо к нужному моменту записи.'
        )

        soft(
            'Основная идея простая: меньше помнить вручную, где что лежит и где ты остановился, '
            'и больше работать непосредственно с самим текстом.'
        )

        add_label(
            'Ra_Reader',
            (
                'Alice',
                11
            ),
            secondary,
            pady=(
                25,
                45
            )
        )

        window.protocol(
            'WM_DELETE_WINDOW',
            self.close_help_window
        )

        window.bind(
            '<Escape>',
            lambda event:
            self.close_help_window()
        )

        window.lift()
        window.focus_force()

    def on_top_right_click(
        self,
        event
    ):
        for button in self.overlay_buttons:
            if (
                button['canvas'] is self.top_canvas
                and button['key'] == '11'
                and abs(
                    button['x'] - event.x
                ) <= 17
                and abs(
                    button['y'] - event.y
                ) <= 17
            ):
                menu = Menu(
                    self.top_canvas,
                    tearoff=0
                )

                menu.add_command(
                    label='Сброс всех настроек',
                    command=self.show_factory_reset_confirmation
                )

                try:
                    menu.tk_popup(
                        event.x_root,
                        event.y_root
                    )
                finally:
                    menu.grab_release()

                return 'break'

    def show_factory_reset_confirmation(self):
        window = tk.Toplevel(
            self.root
        )

        window.title(
            'Сброс настроек'
        )

        window.resizable(
            False,
            False
        )

        window.attributes(
            '-topmost',
            True
        )

        width = 470
        height = 150

        sx = window.winfo_screenwidth()
        sy = window.winfo_screenheight()

        window.geometry(
            f'{width}x{height}'
            f'+{(sx-width)//2}'
            f'+{(sy-height)//2}'
        )

        bg = '#e3e4c9'

        window.configure(
            bg=bg
        )

        label = tk.Label(
            window,
            text=(
                'Все настройки будут сброшены '
                'в исходное состояние.\n'
                'Заметки будут очищены'
            ),
            font=('Alice', 13),
            bg=bg,
            fg='#000000',
            justify='center',
            anchor='center',
            wraplength=420
        )

        label.place(
            x=20,
            y=16,
            width=430,
            height=62
        )

        cancel = tk.Button(
            window,
            text='Отмена',
            font=('Alice', 12),
            bd=0,
            command=window.destroy
        )

        cancel.place(
            x=36,
            y=94,
            width=180,
            height=32
        )

        ok = tk.Button(
            window,
            text='ОК',
            font=('Alice', 12),
            bd=0,
            command=lambda:
            (
                window.destroy(),
                self.factory_reset()
            )
        )

        ok.place(
            x=254,
            y=94,
            width=180,
            height=32
        )

        window.transient(
            self.root
        )

        window.grab_set()
        window.focus_force()

    def factory_reset(self):
        # Close settings preview without restoring it.
        if self.settings_window:
            self.settings_preview_active = False

            try:
                self.settings_window.destroy()
            except Exception:
                pass

            self.settings_window = None
            self.settings_canvas = None
            self.settings_snapshot = None

        # Factory appearance.
        factory_themes = {
            'day': {
                'background': '#ffffff',
                'text': '#000000',
                'secondary': '#555555',
                'line': '#d0d0d0'
            },

            'sepia': {
                'background': '#e3e4c9',
                'text': '#2d2d2d',
                'secondary': '#555555',
                'line': '#bfc0aa'
            },

            'night': {
                'background': '#000000',
                'text': '#eaeaea',
                'secondary': '#aaaaaa',
                'line': '#444444'
            }
        }

        for key, value in factory_themes.items():
            self.THEMES[key].clear()
            self.THEMES[key].update(
                value
            )

        self.theme_name = 'day'

        self.theme_marker_colors = {
            key: self.HIGHLIGHT_COLOR
            for key in self.THEMES
        }

        self.content_font_family = 'Alice'
        self.reader_font_size = 13
        self.reader_text_max_width = (
            self.READER_TEXT_MAX_WIDTH
        )

        self.content_full_justify = False

        self.reader_narrow_mode = True
        self.notes_narrow_mode = True

        self.video_folder = None
        self.audio_folder = None
        self.last_media_file_directory = None

        self.reading_positions = {}
        self.bookmarks = {}
        self.highlights = {}

        self.last_opened_transmission = None
        self.last_opened_book = None
        self.last_opened_project = None
        self.last_opened_external = None

        self.external_files = []
        self.last_file_directory = None

        self.global_search_groups = {
            'books': True,
            'transmissions': True,
            'projects': True,
            'files': True
        }

        self.search_excluded_paths.clear()

        # Старый notes Text нельзя оставлять живым:
        # destroy_notes_widgets() иначе может записать его
        # содержимое обратно в только что очищенный Лист 1.
        if self.notes_text:
            self.notes_loading = True

            try:
                self.notes_text.delete(
                    '1.0',
                    tk.END
                )

                self.notes_text.edit_modified(
                    False
                )
            except Exception:
                pass

            self.notes_loading = False

        self.cancel_notes_save_timer()

        self.notes_sheets = [
            {
                'id': 1,
                'name': 'Лист 1',
                'text': '',
                'bold': [],
                'highlights': []
            }
        ]

        self.notes_current_sheet_id = 1
        self.notes_next_sheet_id = 2

        self.search_active = False
        self.search_query = ''
        self.search_matches = []
        self.search_current_index = -1

        self.global_search_query = ''
        self.global_search_results = []
        self.global_search_page = 0

        self.notes_search_active = False
        self.notes_search_query = ''
        self.notes_search_matches = []
        self.notes_search_current_index = -1

        self.reader_font = (
            'Alice',
            13
        )

        self.reader_font_bold = (
            'Alice',
            13,
            'bold'
        )

        self.rebuild_fade_colors()

        # Delete persistent JSON.
        try:
            if self.config_file.exists():
                self.config_file.unlink()
        except Exception as error:
            print(
                'Ошибка удаления настроек:',
                error
            )

        # Prevent this reset operation itself from recreating
        # settings.json.
        self.factory_reset_pending = True

        self.document_cache = {}
        self.document_cache_ready = False

        self.rebuild_document_cache()

        self.current_screen = 'home'

        self.apply_theme_to_widgets()
        self.draw_current_screen(
            10
        )

        try:
            self.root.state(
                'zoomed'
            )
        except Exception:
            pass

    def build_overlay(self):
        width = (
            self.root.winfo_width()
        )

        if width < 60:
            return

        self.top_canvas.configure(
            bg=self.bg_color()
        )

        self.bottom_canvas.configure(
            bg=self.bg_color()
        )

        search_was_active = (
            (
                self.current_screen == 'reader'
                and self.search_active
            )
            or
            (
                self.current_screen == 'notes'
                and self.notes_search_active
            )
        )

        # -----------------------------------------------------
        # Preserve search Entry values before rebuilding.
        # -----------------------------------------------------

        if self.search_entry:
            try:
                self.search_query = (
                    self.search_entry.get()
                )
            except Exception:
                pass

            try:
                self.search_entry.destroy()
            except Exception:
                pass

            self.search_entry = None

        if self.notes_search_entry:
            try:
                self.notes_search_query = (
                    self.notes_search_entry.get()
                )
            except Exception:
                pass

            try:
                self.notes_search_entry.destroy()
            except Exception:
                pass

            self.notes_search_entry = None

        self.top_canvas.delete(
            'all'
        )

        self.bottom_canvas.delete(
            'all'
        )

        self.overlay_buttons = []
        self.overlay_hover = None

        self.bookmark_marker_items = []
        self.bookmark_marker_images = []
        self.search_marker_items = []

        self.bottom_tc_item = None
        self.bottom_pct_item = None

        self.runner_item = None
        self.line_item = None
        self.theme_underline_item = None

        self.continue_item = None
        self.continue_hover = False

        self.search_box_item = None
        self.search_count_item = None

        self.last_overlay_width = (
            width
        )

        positions = (
            self.get_top_icon_positions(
                width
            )
        )

        self.search_layout = 'wide'
        self.search_hide_secondary = False
        self.search_hide_primary = False

        search_geometry = None

        if search_was_active:
            (
                self.search_layout,
                self.search_hide_secondary,
                self.search_hide_primary,
                search_geometry
            ) = self.determine_search_layout(
                width
            )

        else:
            (
                self.search_hide_secondary,
                self.search_hide_primary
            ) = self.get_general_top_visibility(
                width
            )

        # -----------------------------------------------------
        # Right primary: 10 / 11
        # -----------------------------------------------------

        if not self.search_hide_primary:
            self.add_overlay_button(
                self.top_canvas,
                '10',
                positions['10'],
                self.TOP_ICON_Y,
                self.open_help_window
            )

            self.add_overlay_button(
                self.top_canvas,
                '11',
                positions['11'],
                self.TOP_ICON_Y,
                self.open_settings_window
            )

        # -----------------------------------------------------
        # Themes
        # -----------------------------------------------------

        if not self.search_hide_secondary:
            self.add_overlay_button(
                self.top_canvas,
                '14',
                positions['14'],
                self.TOP_ICON_Y,
                lambda:
                self.set_theme('day')
            )

            self.add_overlay_button(
                self.top_canvas,
                '13',
                positions['13'],
                self.TOP_ICON_Y,
                lambda:
                self.set_theme('sepia')
            )

            self.add_overlay_button(
                self.top_canvas,
                '12',
                positions['12'],
                self.TOP_ICON_Y,
                lambda:
                self.set_theme('night')
            )

            theme_key = {
                'day': '14',
                'sepia': '13',
                'night': '12'
            }.get(
                self.theme_name,
                '14'
            )

            self.theme_underline_item = (
                self.top_canvas.create_image(
                    positions[
                        theme_key
                    ],
                    self.THEME_UNDERLINE_Y,
                    image=self.photo_frames[
                        '26'
                    ][10],
                    anchor='center'
                )
            )

        # -----------------------------------------------------
        # Left primary: home / back
        # -----------------------------------------------------

        if (
            self.current_screen != 'home'
            and not self.search_hide_primary
        ):
            self.add_overlay_button(
                self.top_canvas,
                '16',
                positions['16'],
                self.TOP_ICON_Y,
                self.go_home
            )

            self.add_overlay_button(
                self.top_canvas,
                '17',
                positions['17'],
                self.TOP_ICON_Y,
                self.go_back
            )

        # -----------------------------------------------------
        # Reader
        # -----------------------------------------------------

        if self.current_screen == 'reader':
            if not self.search_hide_secondary:
                self.add_overlay_button(
                    self.top_canvas,
                    '18',
                    positions['18'],
                    self.TOP_ICON_Y,
                    self.scroll_page_up
                )

                self.add_overlay_button(
                    self.top_canvas,
                    '19',
                    positions['19'],
                    self.TOP_ICON_Y,
                    self.scroll_page_down
                )

            if search_was_active:
                self.create_search_overlay(
                    search_geometry
                )

            else:
                self.add_overlay_button(
                    self.top_canvas,
                    '20',
                    width // 2,
                    self.TOP_ICON_Y,
                    self.open_search
                )

        # -----------------------------------------------------
        # Notes
        # -----------------------------------------------------

        if self.current_screen == 'notes':
            if search_was_active:
                self.create_notes_search_overlay(
                    search_geometry
                )

            else:
                self.add_overlay_button(
                    self.top_canvas,
                    '20',
                    width // 2,
                    self.TOP_ICON_Y,
                    self.open_notes_search
                )

        # -----------------------------------------------------
        # Continue
        # -----------------------------------------------------

        if (
            self.current_screen in (
                'books',
                'transmissions',
                'projects',
                'files'
            )
            and self.has_valid_continue_file()
        ):
            self.continue_item = (
                self.top_canvas.create_image(
                    width // 2,
                    self.CONTINUE_Y,
                    image=self.photo_frames[
                        '24'
                    ][10],
                    anchor='center'
                )
            )

        # -----------------------------------------------------
        # Reader bottom
        # -----------------------------------------------------

        if self.current_screen == 'reader':
            status_text = (
                self.current_timecode
                if self.reader_source_type
                == 'transmission'
                else ''
            )

            self.bottom_tc_item = (
                self.bottom_canvas.create_text(
                    8,
                    self.BOTTOM_TEXT_Y,
                    text=status_text,
                    font=self.status_font,
                    fill=self.secondary_color(),
                    anchor='sw'
                )
            )

            self.add_overlay_button(
                self.bottom_canvas,
                '29',
                self.FILL_X,
                self.BOTTOM_BUTTON_Y,
                self.toggle_selection_highlight
            )

            marks = (
                self.get_current_bookmarks()
            )

            enabled = bool(
                marks
            )

            self.add_overlay_button(
                self.bottom_canvas,
                '27',
                self.PREV_BOOKMARK_X,
                self.BOTTOM_BUTTON_Y,
                (
                    self.goto_previous_bookmark
                    if enabled
                    else None
                ),
                enabled=enabled
            )

            self.add_overlay_button(
                self.bottom_canvas,
                '28',
                self.NEXT_BOOKMARK_X,
                self.BOTTOM_BUTTON_Y,
                (
                    self.goto_next_bookmark
                    if enabled
                    else None
                ),
                enabled=enabled
            )

            self.add_overlay_button(
                self.bottom_canvas,
                '21',
                self.BOOKMARK_X,
                self.BOTTOM_BUTTON_Y,
                self.toggle_bookmark
            )

            x1 = self.LINE_LEFT

            x2 = (
                self.get_reader_line_right()
            )

            if x2 > x1:
                self.line_item = (
                    self.bottom_canvas.create_line(
                        x1,
                        self.LINE_Y,
                        x2,
                        self.LINE_Y,
                        fill=self.line_color(),
                        width=4,
                        capstyle=tk.ROUND
                    )
                )

                self.draw_bookmark_markers(
                    x1,
                    x2
                )

                self.draw_reader_search_markers(
                    x1,
                    x2
                )

                self.runner_item = (
                    self.bottom_canvas.create_image(
                        x1,
                        self.LINE_Y,
                        image=self.photo_frames[
                            '22'
                        ][10],
                        anchor='center'
                    )
                )

            self.bottom_pct_item = (
                self.bottom_canvas.create_text(
                    self.get_reader_percentage_x(),
                    self.BOTTOM_TEXT_Y,
                    text='0%',
                    font=self.status_font,
                    fill=self.secondary_color(),
                    anchor='se'
                )
            )

            # ---------------------------------------------
            # Reader width toggle 41.png
            # ---------------------------------------------

            width_button_x = (
                self.get_reader_width_button_x()
            )

            active_bg_frame = (
                4
                if self.reader_narrow_mode
                else 0
            )

            self.reader_width_button_bg = (
                self.bottom_canvas.create_image(
                    width_button_x,
                    self.BOTTOM_BUTTON_Y,
                    image=self.photo_frames[
                        '15'
                    ][active_bg_frame],
                    anchor='center'
                )
            )

            self.reader_width_button = (
                self.bottom_canvas.create_image(
                    width_button_x,
                    self.BOTTOM_BUTTON_Y,
                    image=self.photo_frames[
                        '41'
                    ][10],
                    anchor='center'
                )
            )

            def reader_width_hover(
                active
            ):
                try:
                    frame = (
                        10
                        if active
                        else (
                            4
                            if self.reader_narrow_mode
                            else 0
                        )
                    )

                    self.bottom_canvas.itemconfig(
                        self.reader_width_button_bg,
                        image=self.photo_frames[
                            '15'
                        ][frame]
                    )
                except Exception:
                    pass

            for item in (
                self.reader_width_button_bg,
                self.reader_width_button
            ):
                self.bottom_canvas.tag_bind(
                    item,
                    '<Enter>',
                    lambda event:
                    reader_width_hover(
                        True
                    )
                )

                self.bottom_canvas.tag_bind(
                    item,
                    '<Leave>',
                    lambda event:
                    reader_width_hover(
                        False
                    )
                )

                self.bottom_canvas.tag_bind(
                    item,
                    '<Button-1>',
                    lambda event:
                    self.toggle_reader_width_mode()
                )

            try:
                self.bottom_canvas.tag_raise(
                    self.reader_width_button_bg
                )

                self.bottom_canvas.tag_raise(
                    self.reader_width_button
                )
            except Exception:
                pass

            self.update_bottom_status()

        # -----------------------------------------------------
        # Notes bottom MUST be last.
        # -----------------------------------------------------

        elif self.current_screen == 'notes':
            self.draw_notes_bottom_bar()

    def draw_reader_search_markers(
        self,
        x1,
        x2
    ):
        self.search_marker_items = []

        if (
            not self.search_active
            or len(
                self.search_query
            )
            < self.SEARCH_MIN_CHARS
            or not self.search_matches
            or not self.reader_content
            or x2 <= x1
        ):
            return

        total = float(
            len(
                self.reader_content
            )
        )

        if total <= 0:
            return

        half_width = (
            self.SEARCH_MARKER_WIDTH
            / 2.0
        )

        half_height = (
            self.SEARCH_MARKER_HEIGHT
            / 2.0
        )

        for start, end in (
            self.search_matches
        ):
            ratio = max(
                0.0,
                min(
                    1.0,
                    start / total
                )
            )

            x = (
                x1
                + ratio
                * (
                    x2 - x1
                )
            )

            item = (
                self.bottom_canvas.create_rectangle(
                    x - half_width,
                    self.LINE_Y
                    - half_height,

                    x + half_width,
                    self.LINE_Y
                    + half_height,

                    fill=(
                        self.SEARCH_MARKER_COLOR
                    ),
                    outline=''
                )
            )

            self.search_marker_items.append(
                item
            )

    # =========================================================
    # OVERLAY HIT / HOVER / CLICK
    # =========================================================

    def hit_overlay_button(
        self,
        canvas,
        x,
        y
    ):
        for index, button in enumerate(
            self.overlay_buttons
        ):
            if (
                button[
                    'canvas'
                ] is canvas
                and button.get(
                    'enabled',
                    True
                )
                and abs(
                    button[
                        'x'
                    ] - x
                ) <= 17
                and abs(
                    button[
                        'y'
                    ] - y
                ) <= 17
            ):
                return index

        return None

    def set_overlay_hover(
        self,
        index
    ):
        if (
            index
            == self.overlay_hover
        ):
            return

        old = (
            self.overlay_hover
        )

        if (
            old is not None
            and old < len(
                self.overlay_buttons
            )
        ):
            button = (
                self.overlay_buttons[
                    old
                ]
            )

            try:
                button[
                    'canvas'
                ].itemconfig(
                    button[
                        'plashka'
                    ],
                    image=self.photo_frames[
                        '15'
                    ][0]
                )

            except Exception:
                pass

        self.overlay_hover = (
            index
        )

        if (
            index is not None
            and index < len(
                self.overlay_buttons
            )
        ):
            button = (
                self.overlay_buttons[
                    index
                ]
            )

            if button.get(
                'enabled',
                True
            ):
                try:
                    button[
                        'canvas'
                    ].itemconfig(
                        button[
                            'plashka'
                        ],
                        image=self.photo_frames[
                            '15'
                        ][10]
                    )

                except Exception:
                    pass

    def update_continue_hover_top(
        self,
        x,
        y
    ):
        if (
            self.continue_item
            is None
        ):
            return False

        hovering = (
            self.is_continue_hit(
                x,
                y
            )
        )

        if (
            hovering
            != self.continue_hover
        ):
            self.continue_hover = (
                hovering
            )

            key = (
                '25'
                if hovering
                else '24'
            )

            try:
                self.top_canvas.itemconfig(
                    self.continue_item,
                    image=self.photo_frames[
                        key
                    ][10]
                )

            except Exception:
                pass

        return hovering

    def on_overlay_motion(
        self,
        event
    ):
        if (
            self.continue_item
            is not None
            and
            self.update_continue_hover_top(
                event.x,
                event.y
            )
        ):
            self.set_overlay_hover(
                None
            )

            return

        self.set_overlay_hover(
            self.hit_overlay_button(
                self.top_canvas,
                event.x,
                event.y
            )
        )

    def on_bottom_motion(
        self,
        event
    ):
        if (
            self.is_dragging_runner
        ):
            return

        self.set_overlay_hover(
            self.hit_overlay_button(
                self.bottom_canvas,
                event.x,
                event.y
            )
        )

    def on_overlay_leave(
        self,
        event
    ):
        self.set_overlay_hover(
            None
        )

        if (
            event.widget
            is self.top_canvas
            and self.continue_item
            is not None
        ):
            self.continue_hover = (
                False
            )

            try:
                self.top_canvas.itemconfig(
                    self.continue_item,
                    image=self.photo_frames[
                        '24'
                    ][10]
                )

            except Exception:
                pass

    def press_overlay_button(
        self,
        index
    ):
        if (
            index is None
            or index >= len(
                self.overlay_buttons
            )
        ):
            return

        button = (
            self.overlay_buttons[
                index
            ]
        )

        if not button.get(
            'enabled',
            True
        ):
            return

        canvas = (
            button[
                'canvas'
            ]
        )

        try:
            canvas.coords(
                button[
                    'plashka'
                ],
                button[
                    'x'
                ],
                button[
                    'y'
                ]
                + self.CLICK_OFFSET
            )

            canvas.coords(
                button[
                    'icon'
                ],
                button[
                    'x'
                ],
                button[
                    'y'
                ]
                + self.CLICK_OFFSET
            )

        except Exception:
            return

        def release():
            try:
                canvas.coords(
                    button[
                        'plashka'
                    ],
                    button[
                        'x'
                    ],
                    button[
                        'y'
                    ]
                )

                canvas.coords(
                    button[
                        'icon'
                    ],
                    button[
                        'x'
                    ],
                    button[
                        'y'
                    ]
                )

            except Exception:
                return

            command = (
                button.get(
                    'command'
                )
            )

            if command:
                command()

        self.root.after(
            self.CLICK_DELAY,
            release
        )

    def on_overlay_click(
        self,
        event
    ):
        if (
            self.continue_item
            is not None
            and
            self.is_continue_hit(
                event.x,
                event.y
            )
        ):
            self.press_continue_reading()

            return

        self.press_overlay_button(
            self.hit_overlay_button(
                self.top_canvas,
                event.x,
                event.y
            )
        )

    # =========================================================
    # CONTINUE
    # =========================================================

    def get_continue_file(self):
        if (
            self.current_screen
            == 'books'
        ):
            return (
                self.last_opened_book
            )

        if (
            self.current_screen
            == 'transmissions'
        ):
            return (
                self.last_opened_transmission
            )

        if (
            self.current_screen
            == 'projects'
        ):
            return (
                self.last_opened_project
            )

        if (
            self.current_screen
            == 'files'
        ):
            return (
                self.last_opened_external
            )

        return None

    def has_valid_continue_file(self):
        path = (
            self.get_continue_file()
        )

        return bool(
            path
            and Path(
                path
            ).exists()
        )

    def is_continue_hit(
        self,
        x,
        y
    ):
        if (
            self.current_screen
            not in (
                'books',
                'transmissions',
                'projects',
                'files'
            )
            or self.continue_item
            is None
        ):
            return False

        center_x = (
            self.root.winfo_width()
            // 2
        )

        return (
            center_x
            - self.CONTINUE_WIDTH // 2
            <= x
            <= center_x
            + self.CONTINUE_WIDTH // 2

            and

            self.CONTINUE_Y
            - self.CONTINUE_HEIGHT // 2
            <= y
            <= self.CONTINUE_Y
            + self.CONTINUE_HEIGHT // 2
        )

    def press_continue_reading(self):
        path = (
            self.get_continue_file()
        )

        if (
            not path
            or not Path(
                path
            ).exists()
            or self.is_transitioning
        ):
            return

        self.reader_from_global_search = (
            False
        )

        self.suppress_reader_position_save = (
            False
        )

        self.global_search_target_position = (
            None
        )

        if (
            self.current_screen
            == 'books'
        ):
            self.remember_books_view()

            self.selected_source_type = (
                'book'
            )

        elif (
            self.current_screen
            == 'transmissions'
        ):
            self.remember_transmissions_view()

            self.selected_source_type = (
                'transmission'
            )

        elif (
            self.current_screen
            == 'projects'
        ):
            self.selected_source_type = (
                'project'
            )

        elif (
            self.current_screen
            == 'files'
        ):
            self.remember_files_view()

            self.selected_source_type = (
                'external'
            )

        else:
            return

        self.selected_file = (
            Path(
                path
            )
        )

        self.change_screen(
            'reader'
        )

    # =========================================================
    # HOME
    # =========================================================

    def draw_home_screen(
        self,
        start_frame=10
    ):
        self.reset_canvas_view()

        width = (
            self.canvas.winfo_width()
        )

        height = (
            self.canvas.winfo_height()
        )

        if width < 100 or height < 100:
            return

        self.canvas.delete(
            'all'
        )

        self.canvas.configure(
            bg=self.bg_color()
        )

        self.canvas.config(
            scrollregion=(
                0,
                0,
                width,
                height
            )
        )

        self.screen_elements = []
        self.highlight_items = []
        self.hover_areas = []

        labels = (
            'Поиск',
            'Чтение',
            'Заметки'
        )

        # -----------------------------------------------------
        # Responsive home geometry.
        #
        # 1. First reduce gaps.
        # 2. Only then scale icons.
        # 3. Label font remains unchanged.
        # -----------------------------------------------------

        original_icon = 188

        preferred_gap = 150
        minimum_gap = 24

        side_margin = 20

        available = max(
            60,
            width - side_margin * 2
        )

        # Width required with original icons.
        preferred_total = (
            original_icon * 3
            + preferred_gap * 2
        )

        if available >= preferred_total:
            icon_size = (
                original_icon
            )

            gap = (
                preferred_gap
            )

        else:
            # Keep icons 188px and shrink gaps first.
            possible_gap = (
                available
                - original_icon * 3
            ) // 2

            if possible_gap >= minimum_gap:
                icon_size = (
                    original_icon
                )

                gap = max(
                    minimum_gap,
                    possible_gap
                )

            else:
                # Gaps reached their minimum.
                gap = (
                    minimum_gap
                )

                icon_size = max(
                    48,
                    (
                        available
                        - gap * 2
                    ) // 3
                )

                icon_size = min(
                    original_icon,
                    icon_size
                )

        total_width = (
            icon_size * 3
            + gap * 2
        )

        start_x = (
            width - total_width
        ) // 2

        center_y = (
            height // 2
        )

        label_offset = 30

        # -----------------------------------------------------
        # Each source image is independently resized.
        #
        # PhotoImage references must survive after this method,
        # therefore store them in self.home_scaled_photos.
        # -----------------------------------------------------

        self.home_scaled_photos = []

        for index in range(3):
            x = (
                start_x
                + icon_size // 2
                + index
                * (
                    icon_size + gap
                )
            )

            # Hover background 04 is scaled proportionally.
            hover_size = max(
                icon_size,
                int(
                    272
                    * (
                        icon_size
                        / 188.0
                    )
                )
            )

            source_hover = (
                self.images[
                    '04'
                ]
            )

            hover_width = max(
                1,
                int(
                    source_hover.width
                    * icon_size
                    / 188.0
                )
            )

            hover_height = max(
                1,
                int(
                    source_hover.height
                    * icon_size
                    / 188.0
                )
            )

            hover_image = source_hover.resize(
                (
                    hover_width,
                    hover_height
                ),
                Image.LANCZOS
            )

            # Build fade frames specifically for responsive home.
            hover_frames = []

            for frame in range(11):
                ratio = (
                    frame / 10.0
                )

                img = hover_image.copy()

                alpha = (
                    img.split()[3].point(
                        lambda value,
                        r=ratio:
                        int(value * r)
                    )
                )

                img.putalpha(
                    alpha
                )

                photo = (
                    ImageTk.PhotoImage(
                        img
                    )
                )

                self.home_scaled_photos.append(
                    photo
                )

                hover_frames.append(
                    photo
                )

            hover_item = (
                self.canvas.create_image(
                    x,
                    center_y + 16,
                    image=hover_frames[0],
                    anchor='center'
                )
            )

            element = {
                'type':
                    'home_scaled',

                'item':
                    hover_item,

                'frames':
                    hover_frames,

                'frame':
                    0,

                'fade_target':
                    0,

                'hover_target':
                    0,

                'animation_id':
                    None,

                'x':
                    x,

                'y':
                    center_y + 16,

                'is_highlight':
                    True
            }

            self.highlight_items.append(
                element
            )

            self.screen_elements.append(
                element
            )

            self.hover_areas.append({
                'left':
                    x - hover_width // 2,

                'top':
                    center_y + 16
                    - hover_height // 2,

                'right':
                    x + hover_width // 2,

                'bottom':
                    center_y + 16
                    + hover_height // 2
            })

            # Main 01/02/03 icon.
            key = f'0{index + 1}'

            source = (
                self.images[
                    key
                ]
            )

            resized = source.resize(
                (
                    icon_size,
                    icon_size
                ),
                Image.LANCZOS
            )

            main_frames = []

            for frame in range(11):
                ratio = (
                    frame / 10.0
                )

                img = resized.copy()

                alpha = (
                    img.split()[3].point(
                        lambda value,
                        r=ratio:
                        int(value * r)
                    )
                )

                img.putalpha(
                    alpha
                )

                photo = (
                    ImageTk.PhotoImage(
                        img
                    )
                )

                self.home_scaled_photos.append(
                    photo
                )

                main_frames.append(
                    photo
                )

            image_item = (
                self.canvas.create_image(
                    x,
                    center_y,
                    image=main_frames[
                        start_frame
                    ],
                    anchor='center'
                )
            )

            self.screen_elements.append({
                'type':
                    'home_scaled',

                'item':
                    image_item,

                'frames':
                    main_frames,

                'frame':
                    start_frame,

                'fade_target':
                    start_frame
            })

            self.add_text_element(
                x,
                center_y
                + icon_size // 2
                + label_offset,
                labels[index],
                start_frame
            )

    def draw_reading_screen(
        self,
        start_frame=10
    ):
        self.reset_canvas_view()

        width = (
            self.canvas.winfo_width()
        )

        height = (
            self.canvas.winfo_height()
        )

        if (
            width < 100
            or height < 100
        ):
            return

        self.canvas.delete(
            'all'
        )

        self.canvas.configure(
            bg=self.bg_color()
        )

        self.canvas.config(
            scrollregion=(
                0,
                0,
                width,
                height
            )
        )

        self.screen_elements = []
        self.highlight_items = []
        self.hover_areas = []

        labels = (
            'Книги',
            'Передачи',
            'Проекты',
            'Файлы'
        )

        icons = (
            '05',
            '06',
            '07',
            '36'
        )

        font = tkfont.Font(
            family='Alice',
            size=self.font_size
        )

        max_text_width = max(
            font.measure(
                value
            )
            for value in labels
        )

        icon_size = 24

        row_height = max(
            icon_size,
            font.metrics(
                'linespace'
            )
        )

        row_spacing = 26
        icon_text_gap = 24

        row_width = (
            icon_size
            + icon_text_gap
            + max_text_width
        )

        total_height = (
            row_height * 4
            + row_spacing * 3
        )

        start_x = (
            width
            - row_width
        ) // 2

        start_y = (
            height
            - total_height
        ) // 2

        center_x = (
            width // 2
        )

        text_x = (
            start_x
            + icon_size
            + icon_text_gap
        )

        for index in range(4):
            cy = (
                start_y
                + row_height // 2
                + index
                * (
                    row_height
                    + row_spacing
                )
            )

            self.add_highlight(
                '09',
                center_x,
                cy
            )

        for index in range(4):
            cy = (
                start_y
                + row_height // 2
                + index
                * (
                    row_height
                    + row_spacing
                )
            )

            icon_x = (
                start_x
                + icon_size // 2
            )

            self.add_image_element(
                icons[
                    index
                ],
                icon_x,
                cy,
                start_frame
            )

            self.add_text_element(
                text_x,
                cy,
                labels[
                    index
                ],
                start_frame,
                anchor='w'
            )

    # =========================================================
    # LIST STATE
    # =========================================================

    def remember_transmissions_view(self):
        if (
            self.current_screen
            != 'transmissions'
        ):
            return

        try:
            view = (
                self.canvas.yview()
            )

            if view:
                self.transmissions_yview = (
                    float(
                        view[0]
                    )
                )

        except Exception:
            pass

    def remember_books_view(self):
        if (
            self.current_screen
            != 'books'
        ):
            return

        try:
            view = (
                self.canvas.yview()
            )

            if view:
                self.books_yview = (
                    float(
                        view[0]
                    )
                )

        except Exception:
            pass

    def remember_files_view(self):
        if (
            self.current_screen
            != 'files'
        ):
            return

        try:
            view = (
                self.canvas.yview()
            )

            if view:
                self.files_yview = (
                    float(
                        view[0]
                    )
                )

        except Exception:
            pass

    # =========================================================
    # BOOKS / TRANSMISSIONS LIST
    # =========================================================

    def show_search_path_menu(
        self,
        event,
        path
    ):
        path = Path(
            path
        )

        excluded = (
            self.is_search_path_excluded(
                path
            )
        )

        menu = Menu(
            self.canvas,
            tearoff=0
        )

        menu.add_command(
            label=(
                'Включить в поиск'
                if excluded
                else
                'Исключить из поиска'
            ),
            command=lambda:
            self.set_search_path_excluded(
                path,
                not excluded
            )
        )

        try:
            menu.tk_popup(
                event.x_root,
                event.y_root
            )
        finally:
            menu.grab_release()

    def show_include_all_search_menu(
        self,
        event
    ):
        if not self.search_excluded_paths:
            return

        menu = Menu(
            self.canvas,
            tearoff=0
        )

        menu.add_command(
            label='Включить всё в поиск',
            command=self.include_all_search_documents
        )

        try:
            menu.tk_popup(
                event.x_root,
                event.y_root
            )
        finally:
            menu.grab_release()

    def on_file_list_search_right_click(
        self,
        event
    ):
        if self.current_screen not in (
            'books',
            'transmissions'
        ):
            return

        x = event.x
        y = self.canvas.canvasy(
            event.y
        )

        for item in self.search_list_hit_items:
            if (
                item['left'] <= x <= item['right']
                and item['top'] <= y <= item['bottom']
            ):
                self.show_search_path_menu(
                    event,
                    item['path']
                )

                return 'break'

        self.show_include_all_search_menu(
            event
        )

        return 'break'

    def get_project_group_paths(
        self,
        label
    ):
        if label == 'Вдвоём наедине':
            result = []

            for number in range(
                1,
                33
            ):
                filename = (
                    '01.md'
                    if number == 1
                    else f'{number:02d}.fb2'
                )

                result.append(
                    self.get_project_file(
                        filename
                    )
                )

            return result

        if label == 'Беседы с Имамом':
            return [
                self.get_project_file(
                    f'Беседы с Имамом {number}.fb2'
                )
                for number in range(
                    1,
                    7
                )
            ]

        return []

    def set_search_group_excluded(
        self,
        paths,
        excluded
    ):
        for path in paths:
            key = str(
                Path(path)
            )

            if excluded:
                self.search_excluded_paths.add(
                    key
                )
            else:
                self.search_excluded_paths.discard(
                    key
                )

        self.factory_reset_pending = False
        self.save_settings()

    def on_project_search_right_click(
        self,
        event
    ):
        if self.current_screen != 'projects':
            return

        index = self.find_project_hit(
            event.x,
            event.y
        )

        if index is None:
            self.show_include_all_search_menu(
                event
            )
            return 'break'

        item = self.project_hit_items[
            index
        ]

        if item['type'] == 'project_heading':
            label = item.get(
                'label',
                ''
            )

            paths = self.get_project_group_paths(
                label
            )

            if not paths:
                return 'break'

            all_excluded = all(
                self.is_search_path_excluded(
                    path
                )
                for path in paths
            )

            menu = Menu(
                self.canvas,
                tearoff=0
            )

            menu.add_command(
                label=(
                    'Включить все передачи в поиск'
                    if all_excluded
                    else
                    'Исключить все передачи из поиска'
                ),
                command=lambda:
                self.set_search_group_excluded(
                    paths,
                    not all_excluded
                )
            )

            # If group is only partially excluded, provide
            # both explicit choices.
            if (
                paths
                and not all_excluded
                and any(
                    self.is_search_path_excluded(
                        path
                    )
                    for path in paths
                )
            ):
                menu.add_command(
                    label='Включить все передачи в поиск',
                    command=lambda:
                    self.set_search_group_excluded(
                        paths,
                        False
                    )
                )

            try:
                menu.tk_popup(
                    event.x_root,
                    event.y_root
                )
            finally:
                menu.grab_release()

            return 'break'

        path = item.get(
            'path'
        )

        if path:
            self.show_search_path_menu(
                event,
                path
            )

        return 'break'

    def draw_file_list_screen(
        self,
        items,
        start_frame,
        last_opened_file,
        restore_view,
        saved_yview
    ):
        width = (
            self.canvas.winfo_width()
        )

        height = (
            self.canvas.winfo_height()
        )

        if (
            width < 100
            or height < 100
        ):
            return

        self.canvas.delete(
            'all'
        )

        self.canvas.configure(
            bg=self.bg_color()
        )

        self.screen_elements = []
        self.highlight_items = []
        self.hover_areas = []
        self.search_list_hit_items = []

        row_height = 36
        row_spacing = 12

        content_height = (
            len(
                items
            )
            * (
                row_height
                + row_spacing
            )
            - row_spacing
            if items
            else 0
        )

        available_height = max(
            0,
            height - 40
        )

        needs_scroll = (
            content_height
            > available_height
        )

        panel_width = min(
            800,
            max(
                300,
                width - 40
            )
        )

        if needs_scroll:
            start_y = 30

            self.canvas.config(
                scrollregion=(
                    0,
                    0,
                    width,
                    max(
                        height,
                        content_height + 60
                    )
                )
            )

            self.scrollbar.pack(
                side=tk.RIGHT,
                fill=tk.Y
            )

        else:
            start_y = (
                height
                - content_height
            ) // 2

            self.canvas.config(
                scrollregion=(
                    0,
                    0,
                    width,
                    height
                )
            )

            self.scrollbar.pack_forget()

        self.canvas.bind(
            '<MouseWheel>',
            self.on_mousewheel
        )

        self.canvas.bind(
            '<Button-4>',
            self.on_mousewheel
        )

        self.canvas.bind(
            '<Button-5>',
            self.on_mousewheel
        )

        start_x = (
            width
            - panel_width
        ) // 2

        center_x = (
            width // 2
        )

        date_x = (
            start_x + 80
        )

        y = (
            start_y
        )

        for item in items:
            cy = (
                y
                + row_height // 2
            )

            self.add_highlight(
                '09',
                center_x,
                cy
            )

            if (
                last_opened_file
                and Path(
                    item[
                        'filepath'
                    ]
                )
                == Path(
                    last_opened_file
                )
            ):
                self.add_image_element(
                    '23',
                    date_x - 60,
                    cy,
                    start_frame
                )

            self.add_text_element(
                date_x,
                cy,
                item[
                    'date'
                ],
                start_frame,
                anchor='w',
                semi_transparent=True
            )

            self.add_text_element(
                date_x + 140,
                cy,
                item[
                    'title'
                ],
                start_frame,
                anchor='w'
            )

            self.search_list_hit_items.append({
                'path':
                    Path(
                        item['filepath']
                    ),

                'left':
                    center_x - panel_width // 2,

                'right':
                    center_x + panel_width // 2,

                'top':
                    y,

                'bottom':
                    y + row_height
            })

            y += (
                row_height
                + row_spacing
            )

        self.canvas.bind(
            '<Button-3>',
            self.on_file_list_search_right_click
        )

        self.root.update_idletasks()

        if needs_scroll:
            if restore_view:
                try:
                    self.canvas.yview_moveto(
                        saved_yview
                    )

                except Exception:
                    self.canvas.yview_moveto(
                        0.0
                    )

            else:
                self.canvas.yview_moveto(
                    0.0
                )

        else:
            self.canvas.yview_moveto(
                0.0
            )

    def draw_books_screen(
        self,
        start_frame=10
    ):
        self.load_books()

        self.draw_file_list_screen(
            self.books_list,
            start_frame,
            self.last_opened_book,
            self.restore_books_view,
            self.books_yview
        )

        self.restore_books_view = (
            False
        )

    def draw_transmissions_screen(
        self,
        start_frame=10
    ):
        self.load_transmissions()

        self.draw_file_list_screen(
            self.transmissions_list,
            start_frame,
            self.last_opened_transmission,
            self.restore_transmissions_view,
            self.transmissions_yview
        )

        self.restore_transmissions_view = (
            False
        )

    # =========================================================
    # EXTERNAL FILES
    # =========================================================

    def add_external_file(self):
        initialdir = None

        if (
            self.last_file_directory
            and Path(
                self.last_file_directory
            ).exists()
        ):
            initialdir = str(
                self.last_file_directory
            )

        filenames = (
            filedialog.askopenfilenames(
                parent=self.root,
                title='Добавить файлы',
                initialdir=initialdir,
                filetypes=[
                    (
                        'Поддерживаемые файлы',
                        '*.txt *.fb2 *.md *.html *.htm *.mhtml *.mht'
                    ),
                    ('TXT', '*.txt'),
                    ('FB2', '*.fb2'),
                    ('Markdown', '*.md'),
                    ('HTML', '*.html *.htm'),
                    ('MHTML', '*.mhtml *.mht')
                ]
            )
        )

        if not filenames:
            return

        known = {
            str(item)
            for item in self.external_files
        }

        for filename in filenames:
            path = Path(
                filename
            )

            self.last_file_directory = (
                path.parent
            )

            if str(path) not in known:
                self.external_files.append(
                    path
                )

                known.add(
                    str(path)
                )

            self.update_document_cache_for_file(
                path,
                'external'
            )

        self.save_settings()

        self.restore_files_view = False

        if self.current_screen == 'files':
            self.draw_files_screen(
                10
            )

            self.build_overlay()

    def remove_external_file(
        self,
        path
    ):
        path = Path(
            path
        )

        key = str(
            path
        )

        self.external_files = [
            item
            for item in self.external_files
            if Path(
                item
            ) != path
        ]

        if (
            self.last_opened_external
            and Path(
                self.last_opened_external
            ) == path
        ):
            self.last_opened_external = None

        # Полностью убираем данные именно этого добавленного
        # документа из внутреннего состояния программы.
        self.remove_document_from_cache(
            path
        )

        self.remove_reader_document_cache_for_file(
            path
        )

        self.reading_positions.pop(
            key,
            None
        )

        self.bookmarks.pop(
            key,
            None
        )

        self.highlights.pop(
            key,
            None
        )

        self.search_excluded_paths.discard(
            key
        )

        # На всякий случай удаляем canonical/Path-вариант,
        # если ранее путь сохранялся в немного другом виде.
        try:
            resolved = str(
                path.resolve()
            )

            for container in (
                self.reading_positions,
                self.bookmarks,
                self.highlights
            ):
                container.pop(
                    resolved,
                    None
                )

            self.search_excluded_paths.discard(
                resolved
            )

            self.document_cache.pop(
                resolved,
                None
            )

        except Exception:
            pass

        self.save_settings()

        if (
            self.current_screen
            == 'search'
            and len(
                self.global_search_query
            ) >= self.SEARCH_MIN_CHARS
        ):
            self.rebuild_global_search_results(
                preserve_scroll=False
            )

        if (
            self.current_screen
            == 'files'
        ):
            self.draw_files_screen(
                10
            )

            self.build_overlay()

    def delete_context_external_file(self):
        if (
            self.context_external_file
            is None
        ):
            return

        path = (
            self.context_external_file
        )

        self.context_external_file = (
            None
        )

        self.remove_external_file(
            path
        )

    def clear_all_external_files(self):
        if not self.external_files:
            return

        paths = [
            Path(value)
            for value in self.external_files
        ]

        for path in paths:
            key = str(
                path
            )

            self.remove_document_from_cache(
                path
            )

            self.remove_reader_document_cache_for_file(
                path
            )

            self.reading_positions.pop(
                key,
                None
            )

            self.bookmarks.pop(
                key,
                None
            )

            self.highlights.pop(
                key,
                None
            )

            self.search_excluded_paths.discard(
                key
            )

            try:
                resolved = str(
                    path.resolve()
                )

                self.document_cache.pop(
                    resolved,
                    None
                )

                self.reading_positions.pop(
                    resolved,
                    None
                )

                self.bookmarks.pop(
                    resolved,
                    None
                )

                self.highlights.pop(
                    resolved,
                    None
                )

                self.search_excluded_paths.discard(
                    resolved
                )

            except Exception:
                pass

        self.external_files = []
        self.last_opened_external = None

        self.files_yview = 0.0
        self.restore_files_view = False

        self.save_settings()

        # Пересобираем global-search results, чтобы удалённые
        # документы немедленно исчезли и оттуда.
        if (
            self.current_screen
            == 'search'
            and len(
                self.global_search_query
            ) >= self.SEARCH_MIN_CHARS
        ):
            self.rebuild_global_search_results(
                preserve_scroll=False
            )

        elif (
            self.current_screen
            == 'files'
        ):
            self.draw_files_screen(
                10
            )

            self.build_overlay()

    def show_clear_external_files_menu(
        self,
        event
    ):
        menu = Menu(
            self.canvas,
            tearoff=0
        )

        menu.add_command(
            label='Очистить весь список',
            command=(
                self.clear_all_external_files
            ),
            state=(
                tk.NORMAL
                if self.external_files
                else tk.DISABLED
            )
        )

        if self.search_excluded_paths:
            menu.add_separator()

            menu.add_command(
                label='Включить всё в поиск',
                command=(
                    self.include_all_search_documents
                )
            )

        try:
            menu.tk_popup(
                event.x_root,
                event.y_root
            )

        finally:
            menu.grab_release()

        return 'break'

    def show_external_file_context_menu(
        self,
        event
    ):
        if self.current_screen != 'files':
            return

        x = event.x

        canvas_y = (
            self.canvas.canvasy(
                event.y
            )
        )

        selected = None

        for item in self.file_hit_items:
            if (
                item.get(
                    'type'
                ) == 'external_file'
                and item['left']
                <= x
                <= item['right']
                and item['top']
                <= canvas_y
                <= item['bottom']
            ):
                selected = item
                break

        # ПКМ вне конкретного файла.
        if selected is None:
            return (
                self.show_clear_external_files_menu(
                    event
                )
            )

        path = Path(
            selected['path']
        )

        self.context_external_file = (
            path
        )

        excluded = (
            self.is_search_path_excluded(
                path
            )
        )

        menu = Menu(
            self.canvas,
            tearoff=0
        )

        menu.add_command(
            label='Удалить файл',
            command=(
                self.delete_context_external_file
            )
        )

        menu.add_separator()

        menu.add_command(
            label=(
                'Включить в поиск'
                if excluded
                else
                'Исключить из поиска'
            ),
            command=lambda:
            self.set_search_path_excluded(
                path,
                not excluded
            )
        )

        menu.add_separator()

        menu.add_command(
            label='Очистить весь список',
            command=(
                self.clear_all_external_files
            ),
            state=(
                tk.NORMAL
                if self.external_files
                else tk.DISABLED
            )
        )

        try:
            menu.tk_popup(
                event.x_root,
                event.y_root
            )

        finally:
            menu.grab_release()

        return 'break'

    def draw_files_screen(
        self,
        start_frame=10
    ):
        width = (
            self.canvas.winfo_width()
        )

        height = (
            self.canvas.winfo_height()
        )

        if (
            width < 100
            or height < 100
        ):
            return

        self.canvas.delete(
            'all'
        )

        self.canvas.configure(
            bg=self.bg_color()
        )

        self.screen_elements = []
        self.highlight_items = []
        self.hover_areas = []

        self.file_hit_items = []

        row_height = 36
        row_spacing = 12

        total_rows = (
            1
            + len(
                self.external_files
            )
        )

        content_height = (
            total_rows
            * (
                row_height
                + row_spacing
            )
            - row_spacing
        )

        available_height = max(
            0,
            height - 40
        )

        needs_scroll = (
            content_height
            > available_height
        )

        center_x = (
            width // 2
        )

        if needs_scroll:
            start_y = 30

            self.canvas.config(
                scrollregion=(
                    0,
                    0,
                    width,
                    max(
                        height,
                        content_height + 60
                    )
                )
            )

            self.scrollbar.pack(
                side=tk.RIGHT,
                fill=tk.Y
            )

        else:
            start_y = (
                height
                - content_height
            ) // 2

            self.canvas.config(
                scrollregion=(
                    0,
                    0,
                    width,
                    height
                )
            )

            self.scrollbar.pack_forget()

        self.canvas.bind(
            '<MouseWheel>',
            self.on_mousewheel
        )

        self.canvas.bind(
            '<Button-4>',
            self.on_mousewheel
        )

        self.canvas.bind(
            '<Button-5>',
            self.on_mousewheel
        )

        self.canvas.bind(
            '<Button-3>',
            self.show_external_file_context_menu
        )

        icon_width = 24
        icon_text_gap = 24

        font = tkfont.Font(
            family='Alice',
            size=self.font_size
        )

        labels = [
            'Добавить файл'
        ] + [
            Path(
                path
            ).stem
            for path
            in self.external_files
        ]

        max_text_width = max(
            font.measure(
                value
            )
            for value in labels
        )

        row_width = (
            icon_width
            + icon_text_gap
            + max_text_width
        )

        content_start_x = (
            width
            - row_width
        ) // 2

        icon_x = (
            content_start_x
            + icon_width // 2
        )

        text_x = (
            content_start_x
            + icon_width
            + icon_text_gap
        )

        y = (
            start_y
        )

        # -----------------------------------------------------
        # Add file
        # -----------------------------------------------------

        cy = (
            y
            + row_height // 2
        )

        self.add_highlight(
            '09',
            center_x,
            cy
        )

        self.add_image_element(
            '37',
            icon_x,
            cy,
            start_frame
        )

        self.add_text_element(
            text_x,
            cy,
            'Добавить файл',
            start_frame,
            anchor='w'
        )

        self.file_hit_items.append({
            'type':
                'add_file',

            'left':
                center_x - 400,

            'right':
                center_x + 400,

            'top':
                y,

            'bottom':
                y + row_height
        })

        y += (
            row_height
            + row_spacing
        )

        # -----------------------------------------------------
        # Added files
        # -----------------------------------------------------

        for value in (
            self.external_files
        ):
            path = (
                Path(
                    value
                )
            )

            cy = (
                y
                + row_height // 2
            )

            self.add_highlight(
                '09',
                center_x,
                cy
            )

            if (
                self.last_opened_external
                and path
                == Path(
                    self.last_opened_external
                )
            ):
                self.add_image_element(
                    '23',
                    icon_x,
                    cy,
                    start_frame
                )

            # Extension deliberately omitted.
            self.add_text_element(
                text_x,
                cy,
                path.stem,
                start_frame,
                anchor='w'
            )

            self.file_hit_items.append({
                'type':
                    'external_file',

                'path':
                    path,

                'left':
                    center_x - 400,

                'right':
                    center_x + 400,

                'top':
                    y,

                'bottom':
                    y + row_height
            })

            y += (
                row_height
                + row_spacing
            )

        self.root.update_idletasks()

        if needs_scroll:
            if (
                self.restore_files_view
            ):
                try:
                    self.canvas.yview_moveto(
                        self.files_yview
                    )

                except Exception:
                    self.canvas.yview_moveto(
                        0.0
                    )

            else:
                self.canvas.yview_moveto(
                    0.0
                )

        else:
            self.canvas.yview_moveto(
                0.0
            )

        self.restore_files_view = (
            False
        )

        self.canvas.bind(
            '<Motion>',
            self.on_files_motion
        )

        self.canvas.bind(
            '<Button-1>',
            self.on_files_click
        )

        self.canvas.bind(
            '<Leave>',
            self.on_files_leave
        )

    def get_files_hit_index(
        self,
        x,
        y
    ):
        canvas_y = (
            self.canvas.canvasy(
                y
            )
        )

        for index, item in enumerate(
            self.file_hit_items
        ):
            if (
                item[
                    'left'
                ] <= x
                <= item[
                    'right'
                ]
                and
                item[
                    'top'
                ] <= canvas_y
                <= item[
                    'bottom'
                ]
            ):
                return index

        return None

    def on_files_motion(
        self,
        event
    ):
        if (
            self.current_screen
            != 'files'
        ):
            return

        index = (
            self.get_files_hit_index(
                event.x,
                event.y
            )
        )

        if (
            index
            != self.current_hover
        ):
            if (
                self.current_hover
                is not None
                and self.current_hover
                < len(
                    self.highlight_items
                )
            ):
                self.on_item_leave(
                    self.current_hover
                )

            self.current_hover = (
                index
            )

            if (
                index is not None
                and index < len(
                    self.highlight_items
                )
            ):
                self.on_item_enter(
                    index
                )

    def on_files_leave(
        self,
        event
    ):
        if (
            self.current_hover
            is not None
            and self.current_hover
            < len(
                self.highlight_items
            )
        ):
            self.on_item_leave(
                self.current_hover
            )

        self.current_hover = (
            None
        )

    def on_files_click(
        self,
        event
    ):
        if (
            self.current_screen
            != 'files'
        ):
            return

        index = (
            self.get_files_hit_index(
                event.x,
                event.y
            )
        )

        if (
            index is None
            or index >= len(
                self.file_hit_items
            )
        ):
            return

        item = (
            self.file_hit_items[
                index
            ]
        )

        if (
            item[
                'type'
            ] == 'add_file'
        ):
            self.add_external_file()

            return 'break'

        path = (
            Path(
                item[
                    'path'
                ]
            )
        )

        if not path.exists():
            print(
                'Файл не найден:',
                path
            )

            return 'break'

        self.remember_files_view()

        self.reader_from_global_search = (
            False
        )

        self.suppress_reader_position_save = (
            False
        )

        self.global_search_target_position = (
            None
        )

        self.selected_file = (
            path
        )

        self.selected_source_type = (
            'external'
        )

        self.last_opened_external = (
            path
        )

        self.save_settings()

        self.change_screen(
            'reader'
        )

        return 'break'

    # =========================================================
    # END PART 2/4
    # PART 3 STARTS WITH NOTES
    # =========================================================
    # =========================================================
    # NOTES
    # =========================================================

    def open_notes_search(self):
        if self.current_screen != 'notes':
            return

        self.notes_search_active = True
        self.build_overlay()

        if self.notes_search_entry:
            self.notes_search_entry.focus_set()
            self.notes_search_entry.icursor(
                tk.END
            )

    def close_notes_search(self):
        if not self.notes_search_active:
            return

        self.notes_search_active = False
        self.notes_search_query = ''
        self.notes_search_matches = []
        self.notes_search_current_index = -1

        if self.notes_search_entry:
            try:
                self.notes_search_entry.destroy()
            except Exception:
                pass

            self.notes_search_entry = None

        if self.notes_text:
            try:
                self.notes_text.tag_remove(
                    'notes_search_match',
                    '1.0',
                    tk.END
                )

                self.notes_text.tag_remove(
                    'notes_search_current',
                    '1.0',
                    tk.END
                )
            except Exception:
                pass

        self.build_overlay()

        if self.notes_text:
            self.notes_text.focus_set()

    def notes_search_copy(self):
        if not self.notes_search_entry:
            return

        try:
            if not self.notes_search_entry.selection_present():
                return

            first = self.notes_search_entry.index(
                tk.SEL_FIRST
            )

            last = self.notes_search_entry.index(
                tk.SEL_LAST
            )

            value = self.notes_search_entry.get()[
                first:last
            ]

            self.root.clipboard_clear()
            self.root.clipboard_append(
                value
            )
        except Exception:
            pass

    def notes_search_cut(self):
        if not self.notes_search_entry:
            return

        try:
            if not self.notes_search_entry.selection_present():
                return

            first = self.notes_search_entry.index(
                tk.SEL_FIRST
            )

            last = self.notes_search_entry.index(
                tk.SEL_LAST
            )

            value = self.notes_search_entry.get()[
                first:last
            ]

            self.root.clipboard_clear()
            self.root.clipboard_append(
                value
            )

            self.notes_search_entry.delete(
                first,
                last
            )

            self.notes_search_query = (
                self.notes_search_entry.get()
            )

            self.rebuild_notes_search_matches()

        except Exception:
            pass

    def notes_search_paste(self):
        if not self.notes_search_entry:
            return 'break'

        try:
            value = self.root.clipboard_get()
        except tk.TclError:
            return 'break'

        try:
            if self.notes_search_entry.selection_present():
                self.notes_search_entry.delete(
                    tk.SEL_FIRST,
                    tk.SEL_LAST
                )
        except Exception:
            pass

        position = self.notes_search_entry.index(
            tk.INSERT
        )

        self.notes_search_entry.insert(
            position,
            value
        )

        self.notes_search_query = (
            self.notes_search_entry.get()
        )

        self.rebuild_notes_search_matches()

        return 'break'

    def on_notes_search_ctrl_key(
        self,
        event
    ):
        code = getattr(
            event,
            'keycode',
            None
        )

        char = (
            getattr(
                event,
                'char',
                ''
            ) or ''
        ).lower()

        if code == 65 or char in ('a', 'ф'):
            if self.notes_search_entry:
                self.notes_search_entry.selection_range(
                    0,
                    tk.END
                )

                self.notes_search_entry.icursor(
                    tk.END
                )

            return 'break'

        if code == 67 or char in ('c', 'с'):
            self.notes_search_copy()
            return 'break'

        if code == 88 or char in ('x', 'ч'):
            self.notes_search_cut()
            return 'break'

        if code == 86 or char in ('v', 'м'):
            return self.notes_search_paste()

    def show_notes_search_context_menu(
        self,
        event
    ):
        if not self.notes_search_entry:
            return 'break'

        menu = Menu(
            self.notes_search_entry,
            tearoff=0
        )

        selected = False

        try:
            selected = (
                self.notes_search_entry.selection_present()
            )
        except Exception:
            pass

        menu.add_command(
            label='Вырезать',
            command=self.notes_search_cut,
            state=(
                tk.NORMAL
                if selected
                else tk.DISABLED
            )
        )

        menu.add_command(
            label='Копировать',
            command=self.notes_search_copy,
            state=(
                tk.NORMAL
                if selected
                else tk.DISABLED
            )
        )

        menu.add_command(
            label='Вставить',
            command=self.notes_search_paste
        )

        try:
            menu.tk_popup(
                event.x_root,
                event.y_root
            )

        finally:
            menu.grab_release()

        return 'break'

    def get_notes_search_counter_text(self):
        if (
            len(self.notes_search_query)
            < self.SEARCH_MIN_CHARS
        ):
            return ''

        total = len(
            self.notes_search_matches
        )

        if not total:
            return '0/0'

        return (
            f'{self.notes_search_current_index + 1}'
            f'/{total}'
        )

    def update_notes_search_counter(self):
        if self.notes_search_count_item is None:
            return

        try:
            self.top_canvas.itemconfig(
                self.notes_search_count_item,
                text=(
                    self.get_notes_search_counter_text()
                ),
                fill=self.secondary_color()
            )
        except Exception:
            pass

    def rebuild_notes_search_matches(self):
        self.notes_search_matches = []
        self.notes_search_current_index = -1

        if not self.notes_text:
            return

        query = (
            self.notes_search_query
        )

        if (
            len(query.strip())
            >= self.SEARCH_MIN_CHARS
        ):
            value = self.notes_text.get(
                '1.0',
                'end-1c'
            )

            self.notes_search_matches = (
                self.find_query_matches(
                    value,
                    query
                )
            )

            if self.notes_search_matches:
                self.notes_search_current_index = 0

        self.apply_notes_search_highlights()
        self.update_notes_search_counter()

    def apply_notes_search_highlights(self):
        if not self.notes_text:
            return

        self.notes_text.tag_config(
            'notes_search_match',
            background=(
                self.get_search_normal_display_color()
            )
        )

        self.notes_text.tag_config(
            'notes_search_current',
            background=(
                self.get_search_current_display_color()
            )
        )

        self.notes_text.tag_remove(
            'notes_search_match',
            '1.0',
            tk.END
        )

        self.notes_text.tag_remove(
            'notes_search_current',
            '1.0',
            tk.END
        )

        for index, (start, end) in enumerate(
            self.notes_search_matches
        ):
            tag = (
                'notes_search_current'
                if index
                == self.notes_search_current_index
                else
                'notes_search_match'
            )

            self.notes_text.tag_add(
                tag,
                f'1.0 + {start} chars',
                f'1.0 + {end} chars'
            )

        if (
            self.notes_search_matches
            and
            self.notes_search_current_index >= 0
        ):
            position = (
                self.notes_search_matches[
                    self.notes_search_current_index
                ][0]
            )

            self.notes_text.see(
                f'1.0 + {position} chars'
            )

    def on_notes_search_key_release(
        self,
        event=None
    ):
        if not self.notes_search_entry:
            return

        if (
            event is not None
            and event.keysym in (
                'Return',
                'Shift_L',
                'Shift_R',
                'Left',
                'Right',
                'Up',
                'Down',
                'Home',
                'End'
            )
        ):
            return

        self.notes_search_query = (
            self.notes_search_entry.get()
        )

        self.rebuild_notes_search_matches()

    def notes_search_next(self):
        if not self.notes_search_matches:
            return 'break'

        self.notes_search_current_index = (
            (
                self.notes_search_current_index + 1
            )
            % len(
                self.notes_search_matches
            )
        )

        self.apply_notes_search_highlights()
        self.update_notes_search_counter()

        if self.notes_search_entry:
            self.notes_search_entry.focus_set()

        return 'break'

    def notes_search_previous(self):
        if not self.notes_search_matches:
            return 'break'

        self.notes_search_current_index = (
            (
                self.notes_search_current_index - 1
            )
            % len(
                self.notes_search_matches
            )
        )

        self.apply_notes_search_highlights()
        self.update_notes_search_counter()

        if self.notes_search_entry:
            self.notes_search_entry.focus_set()

        return 'break'

    def create_notes_search_overlay(
        self,
        geometry
    ):
        if not geometry:
            return

        center_x = geometry['center_x']

        center_y = (
            self.SEARCH_BOX_TOP
            + self.SEARCH_BOX_HEIGHT // 2
        )

        box_left = geometry['left']
        box_right = geometry['right']
        box_width = geometry['width']
        image_key = geometry['image_key']

        self.top_canvas.create_image(
            center_x,
            center_y,
            image=self.photo_frames[
                image_key
            ][10],
            anchor='center'
        )

        if image_key == '34':
            counter_width = 45

            entry_width = max(
                28,
                box_width
                - self.SEARCH_TEXT_LEFT
                - counter_width
                - 8
            )

            counter_x = (
                box_right - 8
            )

        else:
            counter_width = 75

            entry_width = max(
                50,
                box_width
                - self.SEARCH_TEXT_LEFT
                - counter_width
                - self.SEARCH_TEXT_RIGHT
            )

            counter_x = (
                box_right
                - self.SEARCH_TEXT_RIGHT
            )

        self.notes_search_entry = tk.Entry(
            self.top_canvas,
            font=('Alice', 12),
            bd=0,
            relief=tk.FLAT,
            highlightthickness=0,
            bg=self.bg_color(),
            fg=self.text_color(),
            insertbackground=self.text_color()
        )

        self.notes_search_entry.insert(
            0,
            self.notes_search_query
        )

        self.notes_search_entry.place(
            x=(
                box_left
                + self.SEARCH_TEXT_LEFT
            ),
            y=(
                self.SEARCH_BOX_TOP + 4
            ),
            width=entry_width,
            height=22
        )

        self.notes_search_entry.bind(
            '<KeyRelease>',
            self.on_notes_search_key_release
        )

        self.notes_search_entry.bind(
            '<Return>',
            lambda event:
            self.notes_search_next()
        )

        self.notes_search_entry.bind(
            '<Shift-Return>',
            lambda event:
            self.notes_search_previous()
        )

        self.notes_search_entry.bind(
            '<Control-KeyPress>',
            self.on_notes_search_ctrl_key
        )

        self.notes_search_entry.bind(
            '<Button-3>',
            self.show_notes_search_context_menu
        )

        self.notes_search_count_item = (
            self.top_canvas.create_text(
                counter_x,
                center_y,
                text=(
                    self.get_notes_search_counter_text()
                ),
                font=('Alice', 11),
                fill=self.secondary_color(),
                anchor='e'
            )
        )

        self.add_overlay_button(
            self.top_canvas,
            '31',
            geometry['x31'],
            self.TOP_ICON_Y,
            self.notes_search_previous
        )

        self.add_overlay_button(
            self.top_canvas,
            '32',
            geometry['x32'],
            self.TOP_ICON_Y,
            self.notes_search_next
        )

        self.add_overlay_button(
            self.top_canvas,
            '33',
            geometry['x33'],
            self.TOP_ICON_Y,
            self.close_notes_search
        )

    def get_current_note_sheet(self):
        for sheet in self.notes_sheets:
            if (
                sheet['id']
                == self.notes_current_sheet_id
            ):
                return sheet

        if self.notes_sheets:
            self.notes_current_sheet_id = (
                self.notes_sheets[0]['id']
            )

            return self.notes_sheets[0]

        return None

    def get_note_sheet_by_id(
        self,
        sheet_id
    ):
        for sheet in self.notes_sheets:
            if sheet['id'] == sheet_id:
                return sheet

        return None

    def get_note_text_offset(
        self,
        index
    ):
        if not self.notes_text:
            return 0

        try:
            value = self.notes_text.count(
                '1.0',
                index,
                'chars'
            )

            if value:
                return int(
                    value[0]
                )

        except Exception:
            pass

        return 0

    def get_note_tag_ranges(
        self,
        tag_name
    ):
        if not self.notes_text:
            return []

        result = []

        try:
            ranges = (
                self.notes_text.tag_ranges(
                    tag_name
                )
            )

        except Exception:
            return []

        for index in range(
            0,
            len(ranges),
            2
        ):
            try:
                start = (
                    self.get_note_text_offset(
                        ranges[index]
                    )
                )

                end = (
                    self.get_note_text_offset(
                        ranges[index + 1]
                    )
                )

            except Exception:
                continue

            if end > start:
                result.append(
                    [
                        start,
                        end
                    ]
                )

        return self.merge_ranges(
            result
        )

    def configure_notes_tags(self):
        if not self.notes_text:
            return

        try:
            self.notes_text.tag_config(
                'note_bold',
                font=self.reader_font_bold
            )

            self.notes_text.tag_config(
                'note_highlight',
                background=(
                    self.get_reader_highlight_color()
                )
            )

        except Exception:
            pass

    def save_current_note_sheet(
        self,
        save_settings_now=False
    ):
        if (
            self.notes_loading
            or not self.notes_text
        ):
            return

        sheet = (
            self.get_current_note_sheet()
        )

        if not sheet:
            return

        try:
            text = (
                self.notes_text.get(
                    '1.0',
                    'end-1c'
                )
            )

        except Exception:
            return

        sheet['text'] = text

        sheet['bold'] = (
            self.get_note_tag_ranges(
                'note_bold'
            )
        )

        sheet['highlights'] = (
            self.get_note_tag_ranges(
                'note_highlight'
            )
        )

        if save_settings_now:
            self.save_settings()

    def cancel_notes_save_timer(self):
        if (
            self.notes_save_timer
            is not None
        ):
            try:
                self.root.after_cancel(
                    self.notes_save_timer
                )

            except Exception:
                pass

            self.notes_save_timer = None

    def schedule_notes_save(self):
        if self.notes_loading:
            return

        self.cancel_notes_save_timer()

        self.notes_save_timer = (
            self.root.after(
                self.NOTES_AUTOSAVE_DELAY,
                self.autosave_notes_now
            )
        )

    def autosave_notes_now(self):
        self.notes_save_timer = None

        if (
            self.current_screen
            != 'notes'
        ):
            return

        self.save_current_note_sheet(
            save_settings_now=True
        )

    def on_notes_modified(
        self,
        event=None
    ):
        if not self.notes_text:
            return

        try:
            modified = (
                self.notes_text.edit_modified()
            )

        except Exception:
            return

        if not modified:
            return

        try:
            self.notes_text.edit_modified(
                False
            )

        except Exception:
            pass

        if self.notes_loading:
            return

        self.schedule_notes_save()

    def load_current_note_sheet(self):
        if not self.notes_text:
            return

        sheet = (
            self.get_current_note_sheet()
        )

        if not sheet:
            return

        self.notes_loading = True

        try:
            self.notes_text.delete(
                '1.0',
                tk.END
            )

            self.notes_text.insert(
                '1.0',
                sheet.get(
                    'text',
                    ''
                )
            )

            self.configure_notes_tags()

            text_length = len(
                sheet.get(
                    'text',
                    ''
                )
            )

            for start, end in (
                self.normalize_note_ranges(
                    sheet.get(
                        'bold',
                        []
                    ),
                    text_length
                )
            ):
                self.notes_text.tag_add(
                    'note_bold',
                    f'1.0 + {start} chars',
                    f'1.0 + {end} chars'
                )

            for start, end in (
                self.normalize_note_ranges(
                    sheet.get(
                        'highlights',
                        []
                    ),
                    text_length
                )
            ):
                self.notes_text.tag_add(
                    'note_highlight',
                    f'1.0 + {start} chars',
                    f'1.0 + {end} chars'
                )

            self.notes_text.tag_raise(
                'note_highlight'
            )

            self.notes_text.tag_raise(
                'note_bold'
            )

            self.notes_text.mark_set(
                tk.INSERT,
                tk.END
            )

            self.notes_text.see(
                tk.INSERT
            )

            self.notes_text.edit_modified(
                False
            )

        finally:
            self.notes_loading = False

    # =========================================================
    # NOTES SCREEN
    # =========================================================

    def destroy_notes_widgets(self):
        self.cancel_notes_save_timer()

        if self.notes_text:
            try:
                self.save_current_note_sheet()
            except Exception:
                pass

        if self.notes_search_entry:
            try:
                self.notes_search_entry.destroy()
            except Exception:
                pass

            self.notes_search_entry = None

        if self.notes_container:
            try:
                self.notes_container.destroy()
            except Exception:
                pass

        self.notes_container = None
        self.notes_editor_frame = None
        self.notes_text = None
        self.notes_scrollbar = None

        # Это ссылка на общий bottom_canvas.
        # Сам общий canvas уничтожать нельзя.
        self.notes_bottom_canvas = None

        self.notes_bold_button = None
        self.notes_fill_button = None
        self.notes_add_button = None

        self.notes_width_button = None
        self.notes_width_button_bg = None

        self.notes_tab_items = []

        self.notes_drag_sheet_id = None
        self.notes_drag_start_x = None
        self.notes_drag_active = False
        self.notes_drag_indicator = None

        self.notes_search_active = False

    def apply_notes_width_mode(self):
        if (
            not self.notes_container
            or not self.notes_text
        ):
            return

        editor_frame = getattr(
            self,
            'notes_editor_frame',
            None
        )

        if not editor_frame:
            return

        try:
            self.root.update_idletasks()

            container_width = max(
                1,
                self.notes_container.winfo_width()
            )

            container_height = max(
                1,
                self.notes_container.winfo_height()
            )

            # Если Tk ещё не выдал реальную геометрию,
            # ничего не меняем в этот проход.
            if (
                container_width <= 2
                or container_height <= 2
            ):
                self.root.after_idle(
                    self.apply_notes_width_mode
                )

                return

            # -------------------------------------------------
            # КЛЮЧЕВО:
            #
            # Полностью забываем старые place-параметры.
            # Иначе width из narrow и relwidth из full
            # одновременно продолжают участвовать в layout.
            # -------------------------------------------------

            editor_frame.place_forget()

            if self.notes_narrow_mode:
                target_width = min(
                    container_width,
                    self.reader_text_max_width
                )

                left = max(
                    0,
                    (
                        container_width
                        - target_width
                    ) // 2
                )

                # Только ABSOLUTE geometry.
                editor_frame.place(
                    x=left,
                    y=0,
                    width=target_width,
                    height=container_height
                )

            else:
                # Только ABSOLUTE geometry.
                #
                # Не используем relwidth=1.0, чтобы от
                # предыдущего режима физически не мог
                # сохраниться конфликт width/relwidth.
                editor_frame.place(
                    x=0,
                    y=0,
                    width=container_width,
                    height=container_height
                )

            editor_frame.lift()

        except Exception:
            pass

    def toggle_notes_width_mode(self):
        if (
            self.current_screen
            != 'notes'
        ):
            return

        self.save_current_note_sheet()

        self.notes_narrow_mode = (
            not self.notes_narrow_mode
        )

        self.save_settings()

        # Геометрия editor меняется непосредственно сейчас.
        self.apply_notes_width_mode()

        # 41.png должна сразу изменить active-state.
        self.build_overlay()

        # После overlay ещё раз применяем геометрию уже
        # при окончательных размерах Tk.
        self.root.after_idle(
            self.apply_notes_width_mode
        )

        if self.notes_text:
            self.notes_text.focus_set()

    def on_notes_container_configure(
        self,
        event=None
    ):
        if (
            self.current_screen
            != 'notes'
        ):
            return

        pending = getattr(
            self,
            '_notes_width_layout_pending',
            False
        )

        if pending:
            return

        self._notes_width_layout_pending = True

        def apply():
            self._notes_width_layout_pending = False

            if self.current_screen == 'notes':
                self.apply_notes_width_mode()

        self.root.after_idle(
            apply
        )

    def draw_notes_screen(self):
        self.destroy_notes_widgets()

        if self.canvas.winfo_ismapped():
            self.canvas.pack_forget()

        self.notes_container = Frame(
            self.middle_frame,
            bg=self.bg_color(),
            bd=0,
            highlightthickness=0
        )

        self.notes_container.pack(
            side=tk.LEFT,
            fill=tk.BOTH,
            expand=True
        )

        self.notes_bottom_canvas = (
            self.bottom_canvas
        )

        # -----------------------------------------------------
        # Editor host.
        #
        # notes_container always fills middle_frame.
        # notes_editor_frame can be either:
        # - full width;
        # - centered, max 1000px.
        # -----------------------------------------------------

        self.notes_editor_frame = Frame(
            self.notes_container,
            bg=self.bg_color(),
            bd=0,
            highlightthickness=0
        )

        editor_frame = (
            self.notes_editor_frame
        )

        self.notes_scrollbar = Scrollbar(
            editor_frame,
            orient=tk.VERTICAL
        )

        self.notes_text = Text(
            editor_frame,
            wrap=tk.WORD,
            font=self.reader_font,
            bg=self.bg_color(),
            fg=self.text_color(),
            insertbackground=self.text_color(),
            selectbackground='#7a9ab8',
            selectforeground=self.text_color(),
            relief=tk.FLAT,
            borderwidth=0,
            highlightthickness=0,
            padx=12,
            pady=8,
            undo=True
        )

        self.notes_scrollbar.configure(
            command=self.notes_text.yview
        )

        self.notes_text.configure(
            yscrollcommand=(
                self.notes_scrollbar.set
            )
        )

        self.notes_text.pack(
            side=tk.LEFT,
            fill=tk.BOTH,
            expand=True
        )

        self.notes_scrollbar.pack(
            side=tk.RIGHT,
            fill=tk.Y
        )

        self.configure_notes_tags()

        self.notes_text.bind(
            '<<Modified>>',
            self.on_notes_modified
        )

        self.notes_text.bind(
            '<Button-3>',
            self.show_notes_text_context_menu
        )

        self.notes_text.bind(
            '<Control-Key>',
            self.on_notes_ctrl_key
        )

        self.notes_text.bind(
            '<Key>',
            self.on_notes_key_press,
            add='+'
        )

        self.notes_text.bind(
            '<Control-MouseWheel>',
            self.on_notes_ctrl_mousewheel
        )

        self.notes_text.bind(
            '<Control-Button-4>',
            self.on_notes_ctrl_mousewheel
        )

        self.notes_text.bind(
            '<Control-Button-5>',
            self.on_notes_ctrl_mousewheel
        )

        self.notes_container.bind(
            '<Configure>',
            self.on_notes_container_configure
        )

        self.load_current_note_sheet()

        # Geometry must be calculated after Tk gives the
        # container its real dimensions.
        self.root.update_idletasks()

        self.apply_notes_width_mode()

        self.root.after_idle(
            self.apply_notes_width_mode
        )

        self.root.after_idle(
            self.update_notes_scrollbar_visibility
        )

        if self.notes_text:
            self.notes_text.focus_set()

    def update_notes_scrollbar_visibility(self):
        if (
            not self.notes_text
            or not self.notes_scrollbar
        ):
            return

        try:
            first, last = (
                self.notes_text.yview()
            )

            if (
                first <= 0.0
                and last >= 1.0
            ):
                self.notes_scrollbar.pack_forget()

            else:
                if not self.notes_scrollbar.winfo_ismapped():
                    self.notes_scrollbar.pack(
                        side=tk.RIGHT,
                        fill=tk.Y
                    )

        except Exception:
            pass

    # =========================================================
    # NOTES BOTTOM BAR
    # =========================================================

    def draw_notes_bottom_bar(self):
        if (
            self.current_screen != 'notes'
            or not self.bottom_canvas
        ):
            return

        canvas = self.bottom_canvas

        self.notes_bottom_canvas = (
            canvas
        )

        self.root.update_idletasks()

        width = max(
            1,
            canvas.winfo_width()
        )

        height = max(
            self.BOTTOM_BAR_HEIGHT,
            canvas.winfo_height()
        )

        canvas.configure(
            bg=self.bg_color()
        )

        # 24x24:
        # lower edge = exactly 8 px from window bottom.
        y = (
            height - 20
        )

        # -----------------------------------------------------
        # Formatting icons
        # -----------------------------------------------------

        bold_x = 20
        fill_x = 52

        # 15.png hover backgrounds.
        bold_bg = (
            canvas.create_image(
                bold_x,
                y,
                image=self.photo_frames[
                    '15'
                ][0],
                anchor='center'
            )
        )

        fill_bg = (
            canvas.create_image(
                fill_x,
                y,
                image=self.photo_frames[
                    '15'
                ][0],
                anchor='center'
            )
        )

        self.notes_bold_button = (
            canvas.create_image(
                bold_x,
                y,
                image=self.photo_frames[
                    '40'
                ][10],
                anchor='center'
            )
        )

        self.notes_fill_button = (
            canvas.create_image(
                fill_x,
                y,
                image=self.photo_frames[
                    '29'
                ][10],
                anchor='center'
            )
        )

        def set_hover(
            background,
            active
        ):
            try:
                canvas.itemconfig(
                    background,
                    image=self.photo_frames[
                        '15'
                    ][
                        10
                        if active
                        else 0
                    ]
                )
            except Exception:
                pass

        for item in (
            bold_bg,
            self.notes_bold_button
        ):
            canvas.tag_bind(
                item,
                '<Enter>',
                lambda event,
                bg=bold_bg:
                set_hover(
                    bg,
                    True
                )
            )

            canvas.tag_bind(
                item,
                '<Leave>',
                lambda event,
                bg=bold_bg:
                set_hover(
                    bg,
                    False
                )
            )

        for item in (
            fill_bg,
            self.notes_fill_button
        ):
            canvas.tag_bind(
                item,
                '<Enter>',
                lambda event,
                bg=fill_bg:
                set_hover(
                    bg,
                    True
                )
            )

            canvas.tag_bind(
                item,
                '<Leave>',
                lambda event,
                bg=fill_bg:
                set_hover(
                    bg,
                    False
                )
            )

        canvas.tag_bind(
            self.notes_bold_button,
            '<Button-1>',
            lambda event:
            self.toggle_notes_bold()
        )

        canvas.tag_bind(
            bold_bg,
            '<Button-1>',
            lambda event:
            self.toggle_notes_bold()
        )

        canvas.tag_bind(
            self.notes_fill_button,
            '<Button-1>',
            lambda event:
            self.toggle_notes_highlight()
        )

        canvas.tag_bind(
            fill_bg,
            '<Button-1>',
            lambda event:
            self.toggle_notes_highlight()
        )

        for item in (
            bold_bg,
            self.notes_bold_button
        ):
            canvas.tag_bind(
                item,
                '<Button-3>',
                self.show_notes_format_context_menu
            )

        for item in (
            fill_bg,
            self.notes_fill_button
        ):
            canvas.tag_bind(
                item,
                '<Button-3>',
                self.show_notes_fill_context_menu
            )

        # -----------------------------------------------------
        # Tabs
        #
        # Right side is NOT reserved for + anymore.
        # Tabs use the available width, but enough physical
        # room is left for a 24x24 add icon after last tab.
        # -----------------------------------------------------

        tabs_left = 92

        right_margin = 8

        # icon half = 12; gap before it = 8.
        add_space = 32

        tabs_right = max(
            tabs_left,
            width
            - right_margin
            - add_space
        )

        count = len(
            self.notes_sheets
        )

        self.notes_tab_items = []

        gap = (
            self.NOTES_TAB_GAP
        )

        last_tab_right = (
            tabs_left
        )

        if count > 0:
            usable_width = max(
                count,
                tabs_right
                - tabs_left
                - max(
                    0,
                    count - 1
                ) * gap
            )

            # 130 is the preferred maximum.
            # With many tabs the width is reduced.
            tab_width = max(
                1,
                min(
                    130,
                    usable_width // count
                )
            )

            normal_font = tkfont.Font(
                family='Alice',
                size=11
            )

            bold_font = tkfont.Font(
                family='Alice',
                size=11,
                weight='bold'
            )

            def fit_name(
                value,
                font,
                available
            ):
                available = max(
                    0,
                    int(
                        available
                    ) - 10
                )

                if available <= 0:
                    return ''

                value = str(
                    value
                )

                if font.measure(
                    value
                ) <= available:
                    return value

                dots = '…'

                if font.measure(
                    dots
                ) > available:
                    return ''

                while value:
                    value = value[:-1]

                    if font.measure(
                        value + dots
                    ) <= available:
                        return (
                            value + dots
                        )

                return dots

            x = (
                tabs_left
            )

            for sheet in (
                self.notes_sheets
            ):
                right = min(
                    tabs_right,
                    x + tab_width
                )

                if right <= x:
                    break

                actual_width = (
                    right - x
                )

                current = (
                    sheet['id']
                    == self.notes_current_sheet_id
                )

                font = (
                    bold_font
                    if current
                    else normal_font
                )

                fill = (
                    self.blend_colors(
                        self.text_color(),
                        self.bg_color(),
                        0.12
                    )
                    if current
                    else self.bg_color()
                )

                rectangle = (
                    canvas.create_rectangle(
                        x,
                        y - 15,
                        right,
                        y + 15,
                        fill=fill,
                        outline=self.secondary_color(),
                        width=1
                    )
                )

                text_item = (
                    canvas.create_text(
                        x
                        + actual_width // 2,
                        y,
                        text=fit_name(
                            sheet['name'],
                            font,
                            actual_width
                        ),
                        font=font,
                        fill=self.text_color(),
                        anchor='center'
                    )
                )

                data = {
                    'sheet_id':
                        sheet['id'],

                    'rect':
                        rectangle,

                    'text':
                        text_item,

                    'left':
                        x,

                    'right':
                        right,

                    'center':
                        x
                        + actual_width // 2
                }

                self.notes_tab_items.append(
                    data
                )

                for item in (
                    rectangle,
                    text_item
                ):
                    canvas.tag_bind(
                        item,
                        '<Button-1>',
                        lambda event,
                        sid=sheet['id']:
                        self.on_notes_tab_press(
                            event,
                            sid
                        )
                    )

                    canvas.tag_bind(
                        item,
                        '<B1-Motion>',
                        lambda event,
                        sid=sheet['id']:
                        self.on_notes_tab_drag(
                            event,
                            sid
                        )
                    )

                    canvas.tag_bind(
                        item,
                        '<ButtonRelease-1>',
                        lambda event,
                        sid=sheet['id']:
                        self.on_notes_tab_release(
                            event,
                            sid
                        )
                    )

                    canvas.tag_bind(
                        item,
                        '<Button-3>',
                        lambda event,
                        sid=sheet['id']:
                        self.show_notes_tab_context_menu(
                            event,
                            sid
                        )
                    )

                last_tab_right = (
                    right
                )

                x = (
                    right + gap
                )

        # -----------------------------------------------------
        # ADD 37.png
        #
        # Exactly after the actual rightmost tab.
        # -----------------------------------------------------

        add_x = (
            last_tab_right
            + 8
            + 12
        )

        add_x = min(
            width - 12,
            add_x
        )

        add_x = max(
            fill_x + 32,
            add_x
        )

        add_frame = (
            10
            if len(
                self.notes_sheets
            ) < self.NOTES_MAX_SHEETS
            else 5
        )

        self.notes_add_button = (
            canvas.create_image(
                add_x,
                y,
                image=self.photo_frames[
                    '37'
                ][add_frame],
                anchor='center'
            )
        )

        if (
            len(
                self.notes_sheets
            )
            < self.NOTES_MAX_SHEETS
        ):
            canvas.tag_bind(
                self.notes_add_button,
                '<Button-1>',
                lambda event:
                self.add_note_sheet()
            )

        try:
            canvas.tag_raise(
                self.notes_add_button
            )
        except Exception:
            pass

        if (
            self.notes_drag_indicator
            is not None
        ):
            try:
                canvas.tag_raise(
                    self.notes_drag_indicator
                )

                canvas.tag_raise(
                    self.notes_add_button
                )
            except Exception:
                pass

        # =====================================================
        # Notes width toggle — 41.png
        # =====================================================

        width_button_x = max(
            12,
            width - 20
        )

        # Active by default.
        #
        # frame 4 gives a quiet permanent indication.
        # Hover switches 15.png to full frame 10.
        active_bg_frame = (
            4
            if self.notes_narrow_mode
            else 0
        )

        self.notes_width_button_bg = (
            canvas.create_image(
                width_button_x,
                y,
                image=self.photo_frames[
                    '15'
                ][active_bg_frame],
                anchor='center'
            )
        )

        self.notes_width_button = (
            canvas.create_image(
                width_button_x,
                y,
                image=self.photo_frames[
                    '41'
                ][10],
                anchor='center'
            )
        )

        def notes_width_hover(
            active
        ):
            try:
                frame = (
                    10
                    if active
                    else (
                        4
                        if self.notes_narrow_mode
                        else 0
                    )
                )

                canvas.itemconfig(
                    self.notes_width_button_bg,
                    image=self.photo_frames[
                        '15'
                    ][frame]
                )
            except Exception:
                pass

        for item in (
            self.notes_width_button_bg,
            self.notes_width_button
        ):
            canvas.tag_bind(
                item,
                '<Enter>',
                lambda event:
                notes_width_hover(
                    True
                )
            )

            canvas.tag_bind(
                item,
                '<Leave>',
                lambda event:
                notes_width_hover(
                    False
                )
            )

            canvas.tag_bind(
                item,
                '<Button-1>',
                lambda event:
                self.toggle_notes_width_mode()
            )

        try:
            canvas.tag_raise(
                self.notes_width_button_bg
            )

            canvas.tag_raise(
                self.notes_width_button
            )
        except Exception:
            pass

    def get_notes_selection(self):
        if not self.notes_text:
            return None

        try:
            start = (
                self.notes_text.index(
                    tk.SEL_FIRST
                )
            )

            end = (
                self.notes_text.index(
                    tk.SEL_LAST
                )
            )

        except tk.TclError:
            return None

        if (
            self.notes_text.compare(
                start,
                '>=',
                end
            )
        ):
            return None

        return (
            start,
            end
        )

    def notes_selection_has_full_tag(
        self,
        tag_name,
        start,
        end
    ):
        start_offset = (
            self.get_note_text_offset(
                start
            )
        )

        end_offset = (
            self.get_note_text_offset(
                end
            )
        )

        ranges = (
            self.get_note_tag_ranges(
                tag_name
            )
        )

        cursor = (
            start_offset
        )

        for a, b in ranges:
            if b <= cursor:
                continue

            if a > cursor:
                return False

            cursor = max(
                cursor,
                b
            )

            if cursor >= end_offset:
                return True

        return False

    def toggle_notes_bold(self):
        selection = (
            self.get_notes_selection()
        )

        if not selection:
            return

        start, end = (
            selection
        )

        if (
            self.notes_selection_has_full_tag(
                'note_bold',
                start,
                end
            )
        ):
            self.notes_text.tag_remove(
                'note_bold',
                start,
                end
            )

        else:
            self.notes_text.tag_add(
                'note_bold',
                start,
                end
            )

        self.save_current_note_sheet(
            save_settings_now=True
        )

    def toggle_notes_highlight(self):
        selection = (
            self.get_notes_selection()
        )

        if not selection:
            return

        start, end = (
            selection
        )

        if (
            self.notes_selection_has_full_tag(
                'note_highlight',
                start,
                end
            )
        ):
            self.notes_text.tag_remove(
                'note_highlight',
                start,
                end
            )

        else:
            self.notes_text.tag_add(
                'note_highlight',
                start,
                end
            )

        self.save_current_note_sheet(
            save_settings_now=True
        )

    def clear_notes_formatting(self):
        if not self.notes_text:
            return

        self.notes_text.tag_remove(
            'note_bold',
            '1.0',
            tk.END
        )

        # Заливку здесь не трогаем.
        self.save_current_note_sheet(
            save_settings_now=True
        )

    def delete_all_notes_highlights(self):
        if not self.notes_text:
            return

        self.notes_text.tag_remove(
            'note_highlight',
            '1.0',
            tk.END
        )

        self.save_current_note_sheet(
            save_settings_now=True
        )

    def show_notes_format_context_menu(
        self,
        event
    ):
        self.notes_format_menu = Menu(
            self.notes_bottom_canvas,
            tearoff=0
        )

        self.notes_format_menu.add_command(
            label='Очистить форматирование',
            command=(
                self.clear_notes_formatting
            )
        )

        try:
            self.notes_format_menu.tk_popup(
                event.x_root,
                event.y_root
            )

        finally:
            self.notes_format_menu.grab_release()

        return 'break'

    def show_notes_fill_context_menu(
        self,
        event
    ):
        self.notes_fill_menu = Menu(
            self.notes_bottom_canvas,
            tearoff=0
        )

        self.notes_fill_menu.add_command(
            label='Удалить все заливки',
            command=(
                self.delete_all_notes_highlights
            )
        )

        try:
            self.notes_fill_menu.tk_popup(
                event.x_root,
                event.y_root
            )

        finally:
            self.notes_fill_menu.grab_release()

        return 'break'

    # =========================================================
    # NOTES CLIPBOARD / CONTEXT MENU
    # =========================================================

    def notes_cut(self):
        if not self.notes_text:
            return

        try:
            text = (
                self.notes_text.get(
                    tk.SEL_FIRST,
                    tk.SEL_LAST
                )
            )

        except tk.TclError:
            return

        self.root.clipboard_clear()

        self.root.clipboard_append(
            text
        )

        self.notes_text.delete(
            tk.SEL_FIRST,
            tk.SEL_LAST
        )

        self.schedule_notes_save()

    def notes_copy(self):
        if not self.notes_text:
            return

        try:
            text = (
                self.notes_text.get(
                    tk.SEL_FIRST,
                    tk.SEL_LAST
                )
            )

        except tk.TclError:
            return

        self.root.clipboard_clear()

        self.root.clipboard_append(
            text
        )

    def notes_paste(self):
        if not self.notes_text:
            return

        try:
            text = (
                self.root.clipboard_get()
            )

        except tk.TclError:
            return

        try:
            if (
                self.notes_text.tag_ranges(
                    tk.SEL
                )
            ):
                self.notes_text.delete(
                    tk.SEL_FIRST,
                    tk.SEL_LAST
                )

        except Exception:
            pass

        self.notes_text.insert(
            tk.INSERT,
            text
        )

        self.schedule_notes_save()

    def show_notes_text_context_menu(
        self,
        event
    ):
        self.notes_context_menu = Menu(
            self.notes_text,
            tearoff=0
        )

        self.notes_context_menu.add_command(
            label='Вырезать',
            command=self.notes_cut
        )

        self.notes_context_menu.add_command(
            label='Копировать',
            command=self.notes_copy
        )

        self.notes_context_menu.add_command(
            label='Вставить',
            command=self.notes_paste
        )

        self.notes_context_menu.add_separator()

        self.notes_context_menu.add_command(
            label='Сохранить в PNG',
            command=self.save_notes_selection_as_png,
            state=(
                tk.NORMAL
                if self.get_notes_selection()
                else tk.DISABLED
            )
        )

        try:
            self.notes_context_menu.tk_popup(
                event.x_root,
                event.y_root
            )

        finally:
            self.notes_context_menu.grab_release()

        return 'break'

    def on_notes_ctrl_key(
        self,
        event
    ):
        if not self.notes_text:
            return

        code = getattr(
            event,
            'keycode',
            None
        )

        char = (
            getattr(
                event,
                'char',
                ''
            )
            or ''
        ).lower()

        if code == 65 or char in ('a', 'ф'):
            try:
                self.notes_text.tag_add(
                    tk.SEL,
                    '1.0',
                    'end-1c'
                )

                self.notes_text.mark_set(
                    tk.INSERT,
                    'end-1c'
                )

                self.notes_text.see(
                    tk.INSERT
                )

                self.notes_text.focus_set()
            except Exception:
                pass

            return 'break'

        if code == 67 or char in ('c', 'с'):
            self.notes_copy()
            return 'break'

        if code == 88 or char in ('x', 'ч'):
            self.notes_cut()
            return 'break'

        if code == 86 or char in ('v', 'м'):
            self.notes_paste()
            return 'break'

        if code == 87 or char in ('w', 'ц'):
            self.copy_notes_formatted(
                'html'
            )
            return 'break'

        if code == 77 or char in ('m', 'ь'):
            self.copy_notes_formatted(
                'markdown'
            )
            return 'break'

    def on_notes_key_press(
        self,
        event
    ):
        if (
            self.current_screen
            != 'notes'
        ):
            return

        if (
            event.keysym in (
                'plus',
                'equal'
            )
            or event.char in (
                '+',
                '='
            )
        ):
            self.increase_notes_font()

            return 'break'

        if (
            event.keysym in (
                'minus',
                'underscore'
            )
            or event.char in (
                '-',
                '_'
            )
        ):
            self.decrease_notes_font()

            return 'break'

    def on_notes_ctrl_mousewheel(
        self,
        event
    ):
        if (
            self.current_screen
            != 'notes'
        ):
            return

        if (
            getattr(
                event,
                'num',
                None
            ) == 4
            or getattr(
                event,
                'delta',
                0
            ) > 0
        ):
            self.increase_notes_font()

        elif (
            getattr(
                event,
                'num',
                None
            ) == 5
            or getattr(
                event,
                'delta',
                0
            ) < 0
        ):
            self.decrease_notes_font()

        return 'break'

    def increase_notes_font(self):
        self.save_current_note_sheet()

        self.reader_font_size += 1

        self.apply_shared_reader_notes_font()

    def decrease_notes_font(self):
        if (
            self.reader_font_size
            <= 8
        ):
            return

        self.save_current_note_sheet()

        self.reader_font_size -= 1

        self.apply_shared_reader_notes_font()

    def apply_shared_reader_notes_font(self):
        self.reader_font = (
            self.content_font_family,
            self.reader_font_size
        )

        self.reader_font_bold = (
            self.content_font_family,
            self.reader_font_size,
            'bold'
        )

        self.reader_font_italic = (
            self.content_font_family,
            self.reader_font_size,
            'italic'
        )

        if self.notes_text:
            self.notes_text.configure(
                font=self.reader_font
            )

            self.configure_notes_tags()

        if self.text_widget:
            self.text_widget.configure(
                font=self.reader_font
            )

            for tag in (
                'speaker',
                'document_bold',
                'title'
            ):
                self.text_widget.tag_config(
                    tag,
                    font=self.reader_font_bold
                )

        self.save_settings()

    # =========================================================
    # NOTES TABS
    # =========================================================

    def get_next_default_sheet_name(self):
        used_names = {
            str(
                sheet[
                    'name'
                ]
            )
            for sheet
            in self.notes_sheets
        }

        for number in range(
            1,
            1000
        ):
            name = (
                f'Лист {number}'
            )

            if name not in used_names:
                return name

        return (
            f'Лист {self.notes_next_sheet_id}'
        )

    def add_note_sheet(self):
        self.reset_notes_tab_drag()

        if (
            len(self.notes_sheets)
            >= self.NOTES_MAX_SHEETS
        ):
            self.build_overlay()
            return

        self.save_current_note_sheet()

        sheet_id = (
            self.notes_next_sheet_id
        )

        self.notes_next_sheet_id += 1

        sheet = {
            'id':
                sheet_id,

            'name':
                self.get_next_default_sheet_name(),

            'text':
                '',

            'bold':
                [],

            'highlights':
                []
        }

        self.notes_sheets.append(
            sheet
        )

        self.notes_current_sheet_id = (
            sheet_id
        )

        self.save_settings()

        self.load_current_note_sheet()

        self.build_overlay()

        if self.notes_text:
            self.notes_text.focus_set()

    def switch_note_sheet(
        self,
        sheet_id
    ):
        self.reset_notes_tab_drag()

        if (
            sheet_id
            == self.notes_current_sheet_id
        ):
            self.build_overlay()
            return

        if not self.get_note_sheet_by_id(
            sheet_id
        ):
            self.build_overlay()
            return

        self.cancel_notes_save_timer()

        self.save_current_note_sheet(
            save_settings_now=True
        )

        self.notes_current_sheet_id = (
            sheet_id
        )

        self.save_settings()

        self.load_current_note_sheet()

        self.build_overlay()

        if self.notes_text:
            self.notes_text.focus_set()

    def rename_note_sheet(
        self,
        sheet_id
    ):
        self.reset_notes_tab_drag()

        sheet = (
            self.get_note_sheet_by_id(
                sheet_id
            )
        )

        if not sheet:
            return

        new_name = (
            simpledialog.askstring(
                'Переименовать',
                'Название вкладки:',
                initialvalue=(
                    sheet[
                        'name'
                    ]
                ),
                parent=self.root
            )
        )

        if new_name is None:
            self.build_overlay()
            return

        new_name = (
            new_name.strip()
        )

        if not new_name:
            self.build_overlay()
            return

        sheet['name'] = (
            new_name
        )

        self.save_settings()

        if (
            self.current_screen
            == 'notes'
        ):
            self.build_overlay()

    def delete_note_sheet(
        self,
        sheet_id
    ):
        self.reset_notes_tab_drag()

        if len(self.notes_sheets) <= 1:
            self.build_overlay()
            return

        self.cancel_notes_save_timer()
        self.save_current_note_sheet()

        index = None

        for i, sheet in enumerate(
            self.notes_sheets
        ):
            if sheet['id'] == sheet_id:
                index = i
                break

        if index is None:
            self.build_overlay()
            return

        was_current = (
            sheet_id
            == self.notes_current_sheet_id
        )

        self.notes_sheets.pop(
            index
        )

        existing = {
            sheet['id']
            for sheet
            in self.notes_sheets
        }

        if (
            was_current
            or self.notes_current_sheet_id
            not in existing
        ):
            new_index = min(
                index,
                len(self.notes_sheets) - 1
            )

            self.notes_current_sheet_id = (
                self.notes_sheets[
                    new_index
                ]['id']
            )

            self.load_current_note_sheet()

        self.save_settings()

        self.build_overlay()

    def show_notes_tab_context_menu(
        self,
        event,
        sheet_id
    ):
        menu = Menu(
            self.notes_bottom_canvas,
            tearoff=0
        )

        menu.add_command(
            label='Переименовать',
            command=lambda:
            self.rename_note_sheet(
                sheet_id
            )
        )

        menu.add_command(
            label='Удалить',
            command=lambda:
            self.delete_note_sheet(
                sheet_id
            ),
            state=(
                tk.NORMAL
                if len(
                    self.notes_sheets
                ) > 1
                else tk.DISABLED
            )
        )

        try:
            menu.tk_popup(
                event.x_root,
                event.y_root
            )

        finally:
            menu.grab_release()

        return 'break'

    # =========================================================
    # NOTES TAB DRAG
    # =========================================================

    def reset_notes_tab_drag(self):
        self.cancel_notes_tab_animation()

        self.destroy_notes_tab_ghost()

        if (
            self.notes_drag_indicator is not None
            and self.notes_bottom_canvas
        ):
            try:
                self.notes_bottom_canvas.delete(
                    self.notes_drag_indicator
                )
            except Exception:
                pass

        self.notes_drag_indicator = None

        self.notes_drag_sheet_id = None
        self.notes_drag_start_x = None
        self.notes_drag_active = False

        self.notes_drag_origin_index = None
        self.notes_drag_drop_index = None

        self.notes_drag_tab_width = 0
        self.notes_drag_valid_zone = None

    def redraw_notes_bottom_bar_later(self):
        if self.current_screen == 'notes':
            self.build_overlay()

    def _redraw_notes_bottom_bar_now(self):
        return

    def cancel_notes_tab_animation(self):
        animation = getattr(
            self,
            'notes_tab_animation_id',
            None
        )

        if animation is not None:
            try:
                self.root.after_cancel(
                    animation
                )
            except Exception:
                pass

        self.notes_tab_animation_id = None

    def get_notes_drag_sheet(self):
        return self.get_note_sheet_by_id(
            self.notes_drag_sheet_id
        )

    def get_notes_drag_slot_index(
        self,
        pointer_x,
        pointer_y
    ):
        """
        Returns insertion slot in the list AFTER the dragged
        sheet has been removed.

        None means invalid drop area.
        """

        canvas = self.notes_bottom_canvas

        if (
            not canvas
            or not self.notes_tab_items
            or self.notes_drag_origin_index is None
        ):
            return None

        height = max(
            self.BOTTOM_BAR_HEIGHT,
            canvas.winfo_height()
        )

        center_y = (
            height - 20
        )

        # Cursor must remain in a sensible tab strip area.
        if not (
            center_y - 24
            <= pointer_y
            <= center_y + 24
        ):
            return None

        # Build slots using all tabs except dragged tab.
        remaining = [
            tab
            for tab in self.notes_tab_items
            if tab['sheet_id']
            != self.notes_drag_sheet_id
        ]

        if not remaining:
            return 0

        strip_left = (
            remaining[0]['left'] - 30
        )

        strip_right = (
            remaining[-1]['right'] + 30
        )

        if not (
            strip_left
            <= pointer_x
            <= strip_right
        ):
            return None

        # Insertion slot is determined by centers of remaining
        # tabs.
        for index, tab in enumerate(
            remaining
        ):
            if pointer_x < tab['center']:
                return index

        return len(
            remaining
        )

    def get_notes_drag_target_positions(
        self,
        slot
    ):
        """
        Target X positions for non-dragged tabs.

        A hole equal to dragged tab width is inserted at slot.
        """

        if (
            self.notes_drag_origin_index is None
            or not self.notes_tab_items
        ):
            return {}

        dragged_tab = None

        for tab in self.notes_tab_items:
            if (
                tab['sheet_id']
                == self.notes_drag_sheet_id
            ):
                dragged_tab = tab
                break

        if dragged_tab is None:
            return {}

        remaining = [
            tab
            for tab in self.notes_tab_items
            if tab['sheet_id']
            != self.notes_drag_sheet_id
        ]

        if not remaining:
            return {}

        gap = (
            self.NOTES_TAB_GAP
        )

        # Use the actual original slot geometry.
        strip_left = min(
            tab['left']
            for tab
            in self.notes_tab_items
        )

        drag_width = max(
            1,
            dragged_tab['right']
            - dragged_tab['left']
        )

        positions = {}

        cursor = (
            strip_left
        )

        for index in range(
            len(remaining) + 1
        ):
            if index == slot:
                cursor += (
                    drag_width + gap
                )

            if index >= len(remaining):
                break

            tab = (
                remaining[index]
            )

            width = max(
                1,
                tab['right']
                - tab['left']
            )

            positions[
                tab['sheet_id']
            ] = cursor

            cursor += (
                width + gap
            )

        return positions

    def animate_notes_tabs_to(
        self,
        targets,
        final_callback=None
    ):
        """
        Fast easing animation. One animation at a time.
        """

        self.cancel_notes_tab_animation()

        canvas = self.notes_bottom_canvas

        if not canvas:
            return

        steps = 5
        delay = 12

        start_positions = {}

        for tab in self.notes_tab_items:
            if (
                tab['sheet_id']
                == self.notes_drag_sheet_id
            ):
                continue

            if tab['sheet_id'] not in targets:
                continue

            try:
                coords = canvas.coords(
                    tab['rect']
                )

                if len(coords) >= 4:
                    start_positions[
                        tab['sheet_id']
                    ] = (
                        coords[0],
                        coords[2]
                    )
            except Exception:
                pass

        def frame(step):
            ratio = (
                step / float(steps)
            )

            # Smooth ease-out.
            eased = (
                1.0
                - (
                    1.0 - ratio
                ) ** 3
            )

            for tab in self.notes_tab_items:
                sid = tab['sheet_id']

                if (
                    sid not in targets
                    or sid not in start_positions
                ):
                    continue

                old_left, old_right = (
                    start_positions[sid]
                )

                width = (
                    old_right - old_left
                )

                wanted_left = (
                    targets[sid]
                )

                left = (
                    old_left
                    + (
                        wanted_left
                        - old_left
                    ) * eased
                )

                right = (
                    left + width
                )

                try:
                    canvas.coords(
                        tab['rect'],
                        left,
                        self.notes_drag_tab_y - 15,
                        right,
                        self.notes_drag_tab_y + 15
                    )

                    canvas.coords(
                        tab['text'],
                        (
                            left + right
                        ) / 2.0,
                        self.notes_drag_tab_y
                    )
                except Exception:
                    pass

            if step < steps:
                self.notes_tab_animation_id = (
                    self.root.after(
                        delay,
                        lambda:
                        frame(
                            step + 1
                        )
                    )
                )

            else:
                self.notes_tab_animation_id = None

                if final_callback:
                    final_callback()

        frame(1)

    def restore_notes_tabs_during_drag(self):
        """
        Return non-dragged tabs to their original positions
        while the ghost remains attached to the pointer.
        """

        targets = {}

        for tab in self.notes_tab_items:
            if (
                tab['sheet_id']
                == self.notes_drag_sheet_id
            ):
                continue

            targets[
                tab['sheet_id']
            ] = tab[
                'left'
            ]

        self.animate_notes_tabs_to(
            targets
        )

    def create_notes_tab_ghost(self):
        canvas = (
            self.notes_bottom_canvas
        )

        sheet = (
            self.get_notes_drag_sheet()
        )

        if (
            not canvas
            or not sheet
        ):
            return

        tab = None

        for value in self.notes_tab_items:
            if (
                value['sheet_id']
                == self.notes_drag_sheet_id
            ):
                tab = value
                break

        if tab is None:
            return

        width = max(
            1,
            tab['right']
            - tab['left']
        )

        self.notes_drag_tab_width = (
            width
        )

        height = max(
            self.BOTTOM_BAR_HEIGHT,
            canvas.winfo_height()
        )

        y = (
            height - 20
        )

        self.notes_drag_tab_y = (
            y
        )

        current = (
            sheet['id']
            == self.notes_current_sheet_id
        )

        fill = (
            self.blend_colors(
                self.text_color(),
                self.bg_color(),
                0.18
            )
            if current
            else
            self.blend_colors(
                self.text_color(),
                self.bg_color(),
                0.08
            )
        )

        self.notes_drag_ghost_rect = (
            canvas.create_rectangle(
                tab['left'],
                y - 15,
                tab['right'],
                y + 15,
                fill=fill,
                outline=self.GLOBAL_RESULT_BORDER,
                width=1
            )
        )

        # Use exactly currently displayed text, including
        # ellipsis if the tab was narrowed.
        try:
            label = canvas.itemcget(
                tab['text'],
                'text'
            )

            font = canvas.itemcget(
                tab['text'],
                'font'
            )
        except Exception:
            label = sheet['name']
            font = ('Alice', 11)

        self.notes_drag_ghost_text = (
            canvas.create_text(
                (
                    tab['left']
                    + tab['right']
                ) / 2.0,
                y,
                text=label,
                font=font,
                fill=self.text_color(),
                anchor='center'
            )
        )

        # Hide original dragged tab.
        try:
            canvas.itemconfigure(
                tab['rect'],
                state='hidden'
            )

            canvas.itemconfigure(
                tab['text'],
                state='hidden'
            )
        except Exception:
            pass

        canvas.tag_raise(
            self.notes_drag_ghost_rect
        )

        canvas.tag_raise(
            self.notes_drag_ghost_text
        )

    def move_notes_tab_ghost(
        self,
        pointer_x
    ):
        if (
            self.notes_drag_ghost_rect is None
            or self.notes_drag_ghost_text is None
        ):
            return

        canvas = (
            self.notes_bottom_canvas
        )

        if not canvas:
            return

        width = max(
            1,
            self.notes_drag_tab_width
        )

        left = (
            pointer_x
            - width / 2.0
        )

        right = (
            pointer_x
            + width / 2.0
        )

        y = (
            self.notes_drag_tab_y
        )

        try:
            canvas.coords(
                self.notes_drag_ghost_rect,
                left,
                y - 15,
                right,
                y + 15
            )

            canvas.coords(
                self.notes_drag_ghost_text,
                pointer_x,
                y
            )

            canvas.tag_raise(
                self.notes_drag_ghost_rect
            )

            canvas.tag_raise(
                self.notes_drag_ghost_text
            )
        except Exception:
            pass

    def destroy_notes_tab_ghost(self):
        canvas = (
            self.notes_bottom_canvas
        )

        if canvas:
            for item in (
                self.notes_drag_ghost_rect,
                self.notes_drag_ghost_text
            ):
                if item is not None:
                    try:
                        canvas.delete(
                            item
                        )
                    except Exception:
                        pass

        self.notes_drag_ghost_rect = None
        self.notes_drag_ghost_text = None

    def on_notes_tab_press(
        self,
        event,
        sheet_id
    ):
        self.reset_notes_tab_drag()

        if not self.get_note_sheet_by_id(
            sheet_id
        ):
            return

        self.notes_drag_sheet_id = (
            sheet_id
        )

        self.notes_drag_start_x = (
            event.x
        )

        self.notes_drag_active = (
            False
        )

        for index, tab in enumerate(
            self.notes_tab_items
        ):
            if tab['sheet_id'] == sheet_id:
                self.notes_drag_origin_index = (
                    index
                )

                break

    def on_notes_tab_drag(
        self,
        event,
        sheet_id
    ):
        if (
            self.notes_drag_sheet_id
            != sheet_id
        ):
            return

        if self.notes_drag_start_x is None:
            return

        if (
            not self.notes_drag_active
            and abs(
                event.x
                - self.notes_drag_start_x
            ) < 5
        ):
            return

        # -----------------------------------------------------
        # Drag starts.
        # -----------------------------------------------------

        if not self.notes_drag_active:
            self.notes_drag_active = True

            self.create_notes_tab_ghost()

        # Ghost always follows cursor horizontally.
        self.move_notes_tab_ghost(
            event.x
        )

        slot = (
            self.get_notes_drag_slot_index(
                event.x,
                event.y
            )
        )

        # -----------------------------------------------------
        # Invalid area -> close hole again.
        # -----------------------------------------------------

        if slot is None:
            if (
                self.notes_drag_drop_index
                is not None
            ):
                self.notes_drag_drop_index = (
                    None
                )

                self.restore_notes_tabs_during_drag()

            return

        # Same insertion hole: no new animation.
        if (
            slot
            == self.notes_drag_drop_index
        ):
            return

        self.notes_drag_drop_index = (
            slot
        )

        targets = (
            self.get_notes_drag_target_positions(
                slot
            )
        )

        self.animate_notes_tabs_to(
            targets
        )

        # Ghost must remain above moving tabs.
        try:
            self.notes_bottom_canvas.tag_raise(
                self.notes_drag_ghost_rect
            )

            self.notes_bottom_canvas.tag_raise(
                self.notes_drag_ghost_text
            )
        except Exception:
            pass

    def on_notes_tab_release(
        self,
        event,
        sheet_id
    ):
        if (
            self.notes_drag_sheet_id
            != sheet_id
        ):
            self.reset_notes_tab_drag()
            return

        if not self.notes_drag_active:
            self.reset_notes_tab_drag()

            self.switch_note_sheet(
                sheet_id
            )

            return

        # Re-evaluate drop position at the actual release
        # coordinate.
        slot = (
            self.get_notes_drag_slot_index(
                event.x,
                event.y
            )
        )

        origin = (
            self.notes_drag_origin_index
        )

        # -----------------------------------------------------
        # Invalid drop: restore old layout and rebuild.
        # -----------------------------------------------------

        if slot is None:
            self.reset_notes_tab_drag()

            self.build_overlay()

            return

        # -----------------------------------------------------
        # Commit using list with dragged sheet removed.
        # -----------------------------------------------------

        source_index = None

        for index, sheet in enumerate(
            self.notes_sheets
        ):
            if sheet['id'] == sheet_id:
                source_index = index
                break

        if source_index is None:
            self.reset_notes_tab_drag()
            self.build_overlay()
            return

        sheet = self.notes_sheets.pop(
            source_index
        )

        slot = max(
            0,
            min(
                slot,
                len(
                    self.notes_sheets
                )
            )
        )

        self.notes_sheets.insert(
            slot,
            sheet
        )

        self.reset_notes_tab_drag()

        self.save_settings()

        # Final exact geometry comes from the normal tab
        # renderer; no accumulated animation coordinates.
        self.build_overlay()

    def reorder_note_sheet_by_x(
        self,
        sheet_id,
        x
    ):
        # Live drag commits directly in on_notes_tab_release.
        return

    def append_text_to_current_note(
        self,
        value,
        bold_ranges=None
    ):
        if not value:
            return

        sheet = self.get_current_note_sheet()

        if not sheet:
            return

        if (
            self.current_screen == 'notes'
            and self.notes_text
        ):
            self.save_current_note_sheet()

        current = sheet.get(
            'text',
            ''
        )

        prefix = ''

        if current:
            if not current.endswith(
                '\n'
            ):
                prefix += '\n'

            prefix += '\n'

        insertion_start = (
            len(current)
            + len(prefix)
        )

        sheet['text'] = (
            current
            + prefix
            + value
        )

        if bold_ranges:
            saved_bold = list(
                sheet.get(
                    'bold',
                    []
                )
            )

            for start, end in bold_ranges:
                if end > start:
                    saved_bold.append(
                        [
                            insertion_start
                            + int(start),

                            insertion_start
                            + int(end)
                        ]
                    )

            sheet['bold'] = (
                self.merge_ranges(
                    saved_bold
                )
            )

        self.save_settings()

        if (
            self.current_screen == 'notes'
            and self.notes_text
        ):
            self.load_current_note_sheet()

    def transfer_reader_selection_to_notes(
        self
    ):
        ranges = (
            self.get_selected_document_ranges()
        )

        if not ranges:
            return

        effective_bold = (
            self.get_reader_effective_bold_ranges()
        )

        parts = []
        output_bold = []

        output_position = 0

        for start, end in ranges:
            part = (
                self.reader_content[
                    start:end
                ]
            )

            parts.append(
                part
            )

            for a, b in effective_bold:
                left = max(
                    start,
                    a
                )

                right = min(
                    end,
                    b
                )

                if right > left:
                    output_bold.append(
                        [
                            output_position
                            + left
                            - start,

                            output_position
                            + right
                            - start
                        ]
                    )

            output_position += len(
                part
            )

        selected = ''.join(
            parts
        )

        if not selected:
            return

        self.append_text_to_current_note(
            selected,
            bold_ranges=output_bold
        )

        try:
            self.root.bell()
        except Exception:
            pass

    def build_imam_special_bold_ranges(
        self,
        text
    ):
        ranges = []

        first_end = (
            text.find(
                '\n'
            )
        )

        if first_end < 0:
            first_end = len(
                text
            )

        first_end = len(
            text[
                0:first_end
            ].rstrip()
        )

        if first_end > 0:
            ranges.append(
                [
                    0,
                    first_end
                ]
            )

            self.reader_title_range = (
                0,
                first_end
            )

        else:
            self.reader_title_range = None

        line_start = 0

        for line in text.splitlines(
            keepends=True
        ):
            body = (
                line.rstrip(
                    '\r\n'
                )
            )

            match = re.match(
                (
                    r'^'
                    r'([А-ЯЁA-Z]'
                    r'[А-Яа-яЁёA-Za-z'
                    r' \-]{0,60})'
                    r':'
                ),
                body
            )

            if match:
                name_end = (
                    line_start
                    + len(
                        match.group(1)
                    )
                    + 1
                )

                ranges.append(
                    [
                        line_start,
                        name_end
                    ]
                )

            line_start += (
                len(
                    line
                )
            )

        return (
            self.merge_ranges(
                ranges
            )
        )

    # =========================================================
    # PROJECTS
    # =========================================================

    def get_project_file(
        self,
        filename
    ):
        return (
            self.projects_dir
            / filename
        )

    def project_is_last_opened(
        self,
        path
    ):
        if not self.last_opened_project:
            return False

        try:
            return (
                Path(
                    path
                )
                == Path(
                    self.last_opened_project
                )
            )

        except Exception:
            return False

    def add_project_number(
        self,
        number,
        x,
        y,
        path
    ):
        path = (
            Path(
                path
            )
        )

        background = (
            self.canvas.create_image(
                x,
                y,
                image=self.photo_frames[
                    '15'
                ][0],
                anchor='center'
            )
        )

        is_last = (
            self.project_is_last_opened(
                path
            )
        )

        text_item = (
            self.canvas.create_text(
                x,
                y,
                text=str(
                    number
                ),
                font=(
                    (
                        'Alice',
                        13,
                        'bold'
                    )
                    if is_last
                    else (
                        'Alice',
                        13
                    )
                ),
                fill=self.text_color(),
                anchor='center'
            )
        )

        self.project_hit_items.append({
            'type':
                'project_number',

            'path':
                path,

            'bg':
                background,

            'text_item':
                text_item,

            'left':
                x - 17,

            'top':
                y - 17,

            'right':
                x + 17,

            'bottom':
                y + 17
        })

    def add_project_heading(
        self,
        label,
        x,
        y
    ):
        text_item = (
            self.canvas.create_text(
                x,
                y,
                text=label,
                font=self.label_font,
                fill=self.text_color(),
                anchor='center'
            )
        )

        self.project_hit_items.append({
            'type':
                'project_heading',

            'label':
                label,

            'bg':
                None,

            'text_item':
                text_item,

            'left':
                x - 160,

            'top':
                y - 20,

            'right':
                x + 160,

            'bottom':
                y + 20
        })

    def add_project_file_row(
        self,
        label,
        path,
        x,
        y
    ):
        path = (
            Path(
                path
            )
        )

        background = (
            self.canvas.create_image(
                x,
                y,
                image=self.photo_frames[
                    '08'
                ][0],
                anchor='center'
            )
        )

        text_item = (
            self.canvas.create_text(
                x,
                y,
                text=label,
                font=self.label_font,
                fill=self.text_color(),
                anchor='center'
            )
        )

        icon_item = None

        if (
            self.project_is_last_opened(
                path
            )
        ):
            text_width = (
                tkfont.Font(
                    family='Alice',
                    size=self.font_size
                ).measure(
                    label
                )
            )

            icon_item = (
                self.canvas.create_image(
                    x
                    - text_width // 2
                    - 24,
                    y,
                    image=self.photo_frames[
                        '23'
                    ][10],
                    anchor='center'
                )
            )

        self.project_hit_items.append({
            'type':
                'project_file',

            'path':
                path,

            'bg':
                background,

            'text_item':
                text_item,

            'icon_item':
                icon_item,

            'left':
                x - 160,

            'top':
                y - 36,

            'right':
                x + 160,

            'bottom':
                y + 36
        })

    def draw_projects_screen(
        self,
        start_frame=10
    ):
        width = (
            self.canvas.winfo_width()
        )

        height = (
            self.canvas.winfo_height()
        )

        if width < 100:
            width = max(
                100,
                self.middle_frame.winfo_width()
            )

        if height < 100:
            height = max(
                100,
                self.middle_frame.winfo_height()
            )

        self.canvas.delete(
            'all'
        )

        self.canvas.configure(
            bg=self.bg_color()
        )

        self.screen_elements = []
        self.highlight_items = []
        self.hover_areas = []

        self.project_hit_items = []
        self.project_hover_index = None

        total_height = (
            48
            + 4 * 34
            + 48
            + 34
            + 3 * 48
        )

        available = max(
            0,
            height - 30
        )

        needs_scroll = (
            total_height
            > available
        )

        if needs_scroll:
            start_y = 20
        else:
            start_y = (
                height
                - total_height
            ) // 2

        center_x = (
            width // 2
        )

        y = (
            start_y + 24
        )

        # -----------------------------------------------------
        # Вдвоём наедине
        # -----------------------------------------------------

        self.add_project_heading(
            'Вдвоём наедине',
            center_x,
            y
        )

        y += 48

        grid_start_x = (
            center_x
            - (
                7
                * self.PROJECT_NUMBER_GAP
            ) // 2
        )

        for number in range(
            1,
            33
        ):
            row = (
                (number - 1) // 8
            )

            column = (
                (number - 1) % 8
            )

            number_x = (
                grid_start_x
                + column
                * self.PROJECT_NUMBER_GAP
            )

            number_y = (
                y
                + row * 34
                - self.PROJECT_NUMBER_RAISE
            )

            if number == 1:
                filename = (
                    '01.md'
                )
            else:
                filename = (
                    f'{number:02d}.fb2'
                )

            self.add_project_number(
                number,
                number_x,
                number_y,
                self.get_project_file(
                    filename
                )
            )

        y += (
            4 * 34
        )

        # -----------------------------------------------------
        # Беседы с Имамом
        # -----------------------------------------------------

        self.add_project_heading(
            'Беседы с Имамом',
            center_x,
            y
        )

        y += 48

        imam_start_x = (
            center_x
            - (
                5
                * self.PROJECT_NUMBER_GAP
            ) // 2
        )

        for number in range(
            1,
            7
        ):
            number_x = (
                imam_start_x
                + (
                    number - 1
                )
                * self.PROJECT_NUMBER_GAP
            )

            self.add_project_number(
                number,
                number_x,
                y
                - self.PROJECT_NUMBER_RAISE,
                self.get_project_file(
                    (
                        'Беседы с Имамом '
                        f'{number}.fb2'
                    )
                )
            )

        y += 34

        # -----------------------------------------------------
        # Single projects
        # -----------------------------------------------------

        self.add_project_file_row(
            'Единое Зерно',
            self.get_project_file(
                'Единое Зерно.md'
            ),
            center_x,
            y
        )

        y += 48

        self.add_project_file_row(
            'Фильм-расследование',
            self.get_project_file(
                'Фильм-расследование.md'
            ),
            center_x,
            y
        )

        y += 48

        self.add_project_file_row(
            'Исконная физика',
            self.get_project_file(
                'Исконная физика.md'
            ),
            center_x,
            y
        )

        y += 24

        content_bottom = (
            y + 20
        )

        self.canvas.config(
            scrollregion=(
                0,
                0,
                width,
                max(
                    height,
                    content_bottom
                )
            )
        )

        if needs_scroll:
            self.scrollbar.pack(
                side=tk.RIGHT,
                fill=tk.Y
            )

            self.canvas.bind(
                '<MouseWheel>',
                self.on_mousewheel
            )

            self.canvas.bind(
                '<Button-4>',
                self.on_mousewheel
            )

            self.canvas.bind(
                '<Button-5>',
                self.on_mousewheel
            )

        else:
            self.scrollbar.pack_forget()

            self.canvas.unbind(
                '<MouseWheel>'
            )

            self.canvas.unbind(
                '<Button-4>'
            )

            self.canvas.unbind(
                '<Button-5>'
            )

        self.canvas.bind(
            '<Motion>',
            self.on_project_motion
        )

        self.canvas.bind(
            '<Button-1>',
            self.on_project_click
        )

        self.canvas.bind(
            '<Button-3>',
            self.on_project_search_right_click
        )

        self.canvas.bind(
            '<Leave>',
            self.on_project_leave
        )

        self.is_transitioning = (
            False
        )

    def find_project_hit(
        self,
        x,
        y
    ):
        canvas_y = (
            self.canvas.canvasy(
                y
            )
        )

        for index, item in enumerate(
            self.project_hit_items
        ):
            if (
                item[
                    'left'
                ] <= x
                <= item[
                    'right'
                ]
                and
                item[
                    'top'
                ] <= canvas_y
                <= item[
                    'bottom'
                ]
            ):
                return index

        return None

    def set_project_hover(
        self,
        index
    ):
        if (
            index
            == self.project_hover_index
        ):
            return

        old = (
            self.project_hover_index
        )

        if (
            old is not None
            and old < len(
                self.project_hit_items
            )
        ):
            item = (
                self.project_hit_items[
                    old
                ]
            )

            if (
                item.get(
                    'bg'
                )
                is not None
            ):
                try:
                    self.canvas.itemconfig(
                        item[
                            'bg'
                        ],
                        image=(
                            self.photo_frames[
                                '15'
                            ][0]
                            if item[
                                'type'
                            ]
                            == 'project_number'
                            else
                            self.photo_frames[
                                '08'
                            ][0]
                        )
                    )

                except Exception:
                    pass

        self.project_hover_index = (
            index
        )

        if (
            index is not None
            and index < len(
                self.project_hit_items
            )
        ):
            item = (
                self.project_hit_items[
                    index
                ]
            )

            if (
                item.get(
                    'bg'
                )
                is None
            ):
                return

            image = (
                self.photo_frames[
                    '15'
                ][10]
                if item[
                    'type'
                ]
                == 'project_number'
                else
                self.photo_frames[
                    '08'
                ][10]
            )

            try:
                self.canvas.itemconfig(
                    item[
                        'bg'
                    ],
                    image=image
                )

            except Exception:
                pass

    def on_project_motion(
        self,
        event
    ):
        if (
            self.current_screen
            != 'projects'
        ):
            return

        index = (
            self.find_project_hit(
                event.x,
                event.y
            )
        )

        if (
            index is not None
            and self.project_hit_items[
                index
            ][
                'type'
            ] == 'project_heading'
        ):
            index = None

        self.set_project_hover(
            index
        )

    def on_project_leave(
        self,
        event
    ):
        self.set_project_hover(
            None
        )

    def on_project_click(
        self,
        event
    ):
        if (
            self.current_screen
            != 'projects'
        ):
            return

        index = (
            self.find_project_hit(
                event.x,
                event.y
            )
        )

        if (
            index is None
            or index >= len(
                self.project_hit_items
            )
        ):
            return

        item = (
            self.project_hit_items[
                index
            ]
        )

        if (
            item[
                'type'
            ] == 'project_heading'
        ):
            return 'break'

        path = (
            item.get(
                'path'
            )
        )

        if not path:
            return 'break'

        path = (
            Path(
                path
            )
        )

        if not path.exists():
            print(
                'Файл проекта не найден:',
                path
            )

            return 'break'

        self.reader_from_global_search = (
            False
        )

        self.suppress_reader_position_save = (
            False
        )

        self.global_search_target_position = (
            None
        )

        self.selected_file = (
            path
        )

        self.selected_source_type = (
            'project'
        )

        self.reader_source_type = (
            'project'
        )

        self.last_opened_project = (
            path
        )

        self.save_settings()

        self.change_screen(
            'reader'
        )

        return 'break'

    # =========================================================
    # FB2
    # =========================================================

    def get_xml_href(
        self,
        element
    ):
        for key, value in (
            element.attrib.items()
        ):
            if (
                key == 'href'
                or key.endswith(
                    '}href'
                )
            ):
                return value

        return None

    def load_fb2_binary_images(
        self,
        root
    ):
        binaries = {}

        for element in root.iter():
            if (
                self.local_xml_tag(
                    element.tag
                )
                != 'binary'
            ):
                continue

            image_id = (
                element.attrib.get(
                    'id'
                )
            )

            if not image_id:
                continue

            payload = ''.join(
                element.itertext()
            ).strip()

            if not payload:
                continue

            try:
                raw = (
                    base64.b64decode(
                        payload
                    )
                )

                image = (
                    Image.open(
                        io.BytesIO(
                            raw
                        )
                    ).convert(
                        'RGBA'
                    )
                )

                binaries[
                    image_id
                ] = image

            except Exception:
                continue

        return binaries

    def parse_fb2_text(
        self,
        content
    ):
        self.document_italic_ranges = []
        self.timecodes = []
        self.timecode_positions = []

        self.document_bold_ranges = []
        self.document_images = []
        self.document_image_positions = []

        self.reader_title_range = None

        try:
            root = (
                ET.fromstring(
                    content
                )
            )

        except Exception:
            cleaned = re.sub(
                r'<[^>]+>',
                ' ',
                content
            )

            cleaned = (
                html.unescape(
                    cleaned
                )
            )

            cleaned = re.sub(
                r'[ \t]+',
                ' ',
                cleaned
            )

            cleaned = re.sub(
                r'\s*\n\s*',
                '\n',
                cleaned
            )

            result = (
                cleaned.strip()
            )

            if (
                self.reader_is_imam_dialogue
            ):
                self.document_bold_ranges = (
                    self.build_imam_special_bold_ranges(
                        result
                    )
                )

            return result

        binaries = (
            self.load_fb2_binary_images(
                root
            )
        )

        bodies = [
            element
            for element
            in root.iter()
            if (
                self.local_xml_tag(
                    element.tag
                )
                == 'body'
                and not element.attrib.get(
                    'name'
                )
            )
        ]

        if not bodies:
            bodies = [
                element
                for element
                in root.iter()
                if (
                    self.local_xml_tag(
                        element.tag
                    )
                    == 'body'
                )
            ]

        parts = []
        length = 0

        bold_ranges = []
        images = []

        block_tags = {
            'p',
            'subtitle',
            'text-author',
            'v',
            'title'
        }

        def append_text(
            value,
            bold=False
        ):
            nonlocal length

            if not value:
                return

            value = re.sub(
                r'\s+',
                ' ',
                value
            )

            if not value:
                return

            start = (
                length
            )

            parts.append(
                value
            )

            length += (
                len(
                    value
                )
            )

            if bold:
                bold_ranges.append(
                    [
                        start,
                        length
                    ]
                )

        def add_break():
            nonlocal length

            if not parts:
                return

            if (
                parts[-1].endswith(
                    '\n\n'
                )
            ):
                return

            parts.append(
                '\n\n'
            )

            length += 2

        def add_image(
            element
        ):
            href = (
                self.get_xml_href(
                    element
                )
            )

            if not href:
                return

            image_id = (
                href.lstrip(
                    '#'
                )
            )

            source = (
                binaries.get(
                    image_id
                )
            )

            if source is None:
                return

            for item in images:
                if (
                    item[
                        'position'
                    ] == length
                    and
                    item[
                        'id'
                    ] == image_id
                ):
                    return

            images.append({
                'position':
                    length,

                'image':
                    source.copy(),

                'id':
                    image_id
            })

        def walk_inline(
            element,
            inherited_bold=False
        ):
            tag = (
                self.local_xml_tag(
                    element.tag
                )
            )

            bold = (
                inherited_bold
                or tag in (
                    'strong',
                    'b',
                    'title',
                    'subtitle'
                )
            )

            if tag == 'image':
                add_image(
                    element
                )

                return

            if element.text:
                append_text(
                    element.text,
                    bold
                )

            for child in element:
                walk_inline(
                    child,
                    bold
                )

                if child.tail:
                    append_text(
                        child.tail,
                        bold
                    )

        parent_map = {
            child:
                parent
            for parent
            in root.iter()
            for child
            in parent
        }

        for body in bodies:
            for element in (
                body.iter()
            ):
                tag = (
                    self.local_xml_tag(
                        element.tag
                    )
                )

                if tag in block_tags:
                    parent = (
                        parent_map.get(
                            element
                        )
                    )

                    parent_tag = (
                        self.local_xml_tag(
                            parent.tag
                        )
                        if parent is not None
                        else ''
                    )

                    if (
                        parent_tag
                        in block_tags
                    ):
                        continue

                    if parts:
                        add_break()

                    walk_inline(
                        element,
                        False
                    )

                    add_break()

                elif tag == 'image':
                    parent = (
                        parent_map.get(
                            element
                        )
                    )

                    parent_tag = (
                        self.local_xml_tag(
                            parent.tag
                        )
                        if parent is not None
                        else ''
                    )

                    if (
                        parent_tag
                        not in block_tags
                    ):
                        add_image(
                            element
                        )

        raw_text = ''.join(
            parts
        )

        left_trim = (
            len(
                raw_text
            )
            - len(
                raw_text.lstrip()
            )
        )

        text = (
            raw_text.strip()
        )

        adjusted_bold = []

        for start, end in (
            bold_ranges
        ):
            start -= (
                left_trim
            )

            end -= (
                left_trim
            )

            start = max(
                0,
                start
            )

            end = min(
                len(
                    text
                ),
                end
            )

            if end > start:
                adjusted_bold.append(
                    [
                        start,
                        end
                    ]
                )

        adjusted_images = []

        for item in images:
            position = (
                item[
                    'position'
                ]
                - left_trim
            )

            position = max(
                0,
                min(
                    position,
                    len(
                        text
                    )
                )
            )

            adjusted_images.append({
                'position':
                    position,

                'image':
                    item[
                        'image'
                    ],

                'id':
                    item[
                        'id'
                    ]
            })

        if (
            self.reader_is_imam_dialogue
        ):
            adjusted_bold.extend(
                self.build_imam_special_bold_ranges(
                    text
                )
            )

        self.document_bold_ranges = (
            self.merge_ranges(
                adjusted_bold
            )
        )

        self.document_images = sorted(
            adjusted_images,
            key=lambda item:
            item[
                'position'
            ]
        )

        self.document_image_positions = [
            item[
                'position'
            ]
            for item
            in self.document_images
        ]

        return text

    # =========================================================
    # MARKDOWN
    # =========================================================

    def normalize_project_markdown_blank_lines(
        self,
        content
    ):
        content = (
            content
            .replace(
                '\r\n',
                '\n'
            )
            .replace(
                '\r',
                '\n'
            )
        )

        content = re.sub(
            r'\n[ \t]+\n',
            '\n\n',
            content
        )

        content = re.sub(
            r'\n{3,}',
            '\n\n',
            content
        )

        return content

    def parse_markdown_text(
        self,
        content
    ):
        self.document_italic_ranges = []
        self.timecodes = []
        self.timecode_positions = []

        self.document_images = []
        self.document_image_positions = []
        self.document_bold_ranges = []

        self.reader_title_range = None

        if (
            self.is_single_markdown_project(
                self.selected_file
            )
        ):
            content = (
                self.normalize_project_markdown_blank_lines(
                    content
                )
            )

        output = []
        bold_ranges = []

        length = 0

        token_re = re.compile(
            (
                r'('
                r'\*\*.+?\*\*'
                r'|'
                r'__.+?__'
                r')'
            )
        )

        lines = (
            content.splitlines()
        )

        for (
            line_index,
            raw_line
        ) in enumerate(
            lines
        ):
            line = (
                raw_line.strip()
            )

            heading_line = bool(
                re.match(
                    r'^#{1,6}\s+',
                    line
                )
            )

            line = re.sub(
                r'^#{1,6}\s+',
                '',
                line
            )

            line = re.sub(
                r'^\s*[-*+]\s+',
                '',
                line
            )

            line = re.sub(
                r'^\s*\d+\.\s+',
                '',
                line
            )

            line = re.sub(
                r'\[([^\]]+)\]\([^)]+\)',
                r'\1',
                line
            )

            pieces = (
                token_re.split(
                    line
                )
            )

            for piece in pieces:
                is_bold = (
                    (
                        piece.startswith(
                            '**'
                        )
                        and piece.endswith(
                            '**'
                        )
                    )
                    or
                    (
                        piece.startswith(
                            '__'
                        )
                        and piece.endswith(
                            '__'
                        )
                    )
                )

                value = (
                    piece[2:-2]
                    if is_bold
                    else piece
                )

                if not value:
                    continue

                start = (
                    length
                )

                output.append(
                    value
                )

                length += (
                    len(
                        value
                    )
                )

                if (
                    is_bold
                    or heading_line
                ):
                    bold_ranges.append(
                        [
                            start,
                            length
                        ]
                    )

            if (
                line_index
                < len(
                    lines
                ) - 1
            ):
                output.append(
                    '\n'
                )

                length += 1

        raw = ''.join(
            output
        )

        left_trim = (
            len(
                raw
            )
            - len(
                raw.lstrip()
            )
        )

        result = (
            raw.strip()
        )

        if (
            self.is_single_markdown_project(
                self.selected_file
            )
        ):
            result = re.sub(
                r'\n{3,}',
                '\n\n',
                result
            )

        adjusted = []

        for start, end in (
            bold_ranges
        ):
            start -= (
                left_trim
            )

            end -= (
                left_trim
            )

            start = max(
                0,
                start
            )

            end = min(
                len(
                    result
                ),
                end
            )

            if end > start:
                adjusted.append(
                    [
                        start,
                        end
                    ]
                )

        self.document_bold_ranges = (
            self.merge_ranges(
                adjusted
            )
        )

        return result

    # =========================================================
    # HTML
    # =========================================================

    def get_html_companion_dirs(
        self,
        path
    ):
        if not path:
            return []

        path = Path(path)

        candidates = [
            path.parent / path.stem,
            path.parent / (path.stem + '_files'),
            path.parent / (path.stem + '.files'),
            path.parent / (path.stem + '-files')
        ]

        return [
            value
            for value in candidates
            if value.exists()
            and value.is_dir()
        ]

    def load_mhtml_document(
        self,
        path
    ):
        try:
            message = BytesParser(
                policy=policy.default
            ).parsebytes(
                Path(path).read_bytes()
            )
        except Exception:
            return '', {}

        html_content = ''
        resources = {}

        for part in message.walk():
            content_type = (
                part.get_content_type()
            )

            location = (
                part.get(
                    'Content-Location'
                )
                or part.get(
                    'Content-ID'
                )
                or ''
            )

            try:
                payload = (
                    part.get_payload(
                        decode=True
                    )
                    or b''
                )
            except Exception:
                payload = b''

            if content_type == 'text/html' and not html_content:
                charset = (
                    part.get_content_charset()
                    or 'utf-8'
                )

                try:
                    html_content = payload.decode(
                        charset,
                        errors='replace'
                    )
                except Exception:
                    html_content = payload.decode(
                        'utf-8',
                        errors='replace'
                    )

            elif content_type.startswith(
                'image/'
            ):
                try:
                    image = Image.open(
                        io.BytesIO(
                            payload
                        )
                    ).convert(
                        'RGBA'
                    )

                    keys = [
                        location,
                        location.strip('<>'),
                        Path(
                            location
                            .split('?', 1)[0]
                        ).name
                    ]

                    for key in keys:
                        if key:
                            resources[key] = (
                                image.copy()
                            )
                except Exception:
                    pass

        return (
            html_content,
            resources
        )

    def prepare_html_for_reader(
        self,
        content
    ):
        if not content:
            return ''

        content = str(
            content
        )

        # Быстро отрезаем head. На сохранённых страницах
        # именно там часто находятся огромные JS states.
        body_match = re.search(
            r'(?is)<body\b[^>]*>(.*)</body\s*>',
            content
        )

        if body_match:
            content = body_match.group(
                1
            )

        # Удаление script — отдельный самый важный этап.
        content = re.sub(
            (
                r'(?is)'
                r'<script\b[^>]*>'
                r'.*?'
                r'</script\s*>'
            ),
            '',
            content
        )

        for tag in (
            'style',
            'noscript',
            'template',
            'svg'
        ):
            content = re.sub(
                (
                    r'(?is)<'
                    + tag
                    + r'\b[^>]*>'
                    + r'.*?'
                    + r'</'
                    + tag
                    + r'\s*>'
                ),
                '',
                content
            )

        # Prefer article.
        articles = re.findall(
            (
                r'(?is)'
                r'<article\b[^>]*>'
                r'.*?'
                r'</article\s*>'
            ),
            content
        )

        if articles:
            return max(
                articles,
                key=len
            )

        # Habr content marker.
        lower = content.casefold()

        for marker in (
            'post-content-body',
            'article-formatted-body',
            'tm-article-body'
        ):
            position = lower.find(
                marker
            )

            if position >= 0:
                left = content.rfind(
                    '<',
                    0,
                    position
                )

                if left < 0:
                    left = position

                # После удаления scripts этот предел обычно
                # полностью покрывает статью.
                return content[
                    left:
                    min(
                        len(content),
                        left + 3000000
                    )
                ]

        main_match = re.search(
            (
                r'(?is)'
                r'<main\b[^>]*>'
                r'.*?'
                r'</main\s*>'
            ),
            content
        )

        if main_match:
            return main_match.group(
                0
            )

        return content

    def get_html_resource_folders(
        self,
        path
    ):
        if not path:
            return []

        path = Path(
            path
        )

        result = []

        candidates = [
            path.parent
            / path.stem,

            path.parent
            / (
                path.stem
                + '_files'
            ),

            path.parent
            / (
                path.stem
                + '.files'
            ),

            path.parent
            / (
                path.stem
                + '-files'
            )
        ]

        # Chrome / Firefox иногда слегка меняют имя папки.
        #
        # Но здесь НЕТ рекурсивного обхода.
        try:
            stem_key = re.sub(
                r'\W+',
                '',
                path.stem.casefold()
            )

            for child in path.parent.iterdir():
                if not child.is_dir():
                    continue

                child_key = re.sub(
                    r'\W+',
                    '',
                    child.name.casefold()
                )

                if (
                    stem_key
                    and (
                        child_key.startswith(
                            stem_key
                        )
                        or stem_key.startswith(
                            child_key
                        )
                    )
                ):
                    candidates.append(
                        child
                    )

        except Exception:
            pass

        seen = set()

        for folder in candidates:
            try:
                key = str(
                    folder.resolve()
                )
            except Exception:
                key = str(
                    folder
                )

            if key in seen:
                continue

            seen.add(
                key
            )

            try:
                if (
                    folder.exists()
                    and folder.is_dir()
                ):
                    result.append(
                        folder
                    )
            except Exception:
                pass

        return result

    def find_local_html_image(
        self,
        src,
        base_path,
        resource_folders
    ):
        """
        Быстрый поиск картинки.

        Никаких rglob/os.walk.
        """

        if (
            not src
            or not base_path
        ):
            return None

        src = html.unescape(
            str(src)
        ).strip()

        if not src:
            return None

        # Embedded data URI.
        if src.casefold().startswith(
            'data:image/'
        ):
            try:
                header, payload = src.split(
                    ',',
                    1
                )

                if ';base64' in header.casefold():
                    raw = base64.b64decode(
                        payload
                    )

                    return (
                        Image.open(
                            io.BytesIO(
                                raw
                            )
                        )
                        .convert(
                            'RGBA'
                        )
                    )
            except Exception:
                pass

            return None

        clean = (
            src
            .split(
                '#',
                1
            )[0]
            .split(
                '?',
                1
            )[0]
        )

        # file:///C:/...
        if clean.casefold().startswith(
            'file://'
        ):
            try:
                from urllib.parse import (
                    urlparse,
                    unquote
                )

                parsed = urlparse(
                    clean
                )

                local = Path(
                    unquote(
                        parsed.path
                    ).lstrip(
                        '/'
                    )
                    if sys.platform == 'win32'
                    else unquote(
                        parsed.path
                    )
                )

                if (
                    local.exists()
                    and local.is_file()
                ):
                    return (
                        Image.open(
                            local
                        )
                        .convert(
                            'RGBA'
                        )
                    )

            except Exception:
                pass

        # Для https URL локальное имя — последняя часть.
        filename = Path(
            clean.replace(
                '\\',
                '/'
            )
        ).name

        base_path = Path(
            base_path
        )

        # -----------------------------------------------------
        # Точная относительная ссылка.
        # -----------------------------------------------------

        if not re.match(
            r'^[a-z][a-z0-9+.-]*://',
            clean,
            flags=re.IGNORECASE
        ):
            try:
                relative = clean.replace(
                    '/',
                    os.sep
                )

                candidate = (
                    base_path.parent
                    / relative
                )

                if (
                    candidate.exists()
                    and candidate.is_file()
                ):
                    return (
                        Image.open(
                            candidate
                        )
                        .convert(
                            'RGBA'
                        )
                    )

            except Exception:
                pass

        if not filename:
            return None

        # -----------------------------------------------------
        # Только прямой lookup в соседних ресурсных папках.
        # -----------------------------------------------------

        for folder in resource_folders:
            try:
                candidate = (
                    folder
                    / filename
                )

                if (
                    candidate.exists()
                    and candidate.is_file()
                ):
                    return (
                        Image.open(
                            candidate
                        )
                        .convert(
                            'RGBA'
                        )
                    )

            except Exception:
                pass

        return None

    def parse_html_document(
        self,
        content,
        base_path=None,
        embedded_resources=None
    ):
        self.document_bold_ranges = []
        self.document_italic_ranges = []
        self.document_images = []
        self.document_image_positions = []

        embedded_resources = (
            embedded_resources
            or {}
        )

        # Самое важное для больших современных страниц.
        content = (
            self.prepare_html_for_reader(
                content
            )
        )

        resource_folders = (
            self.get_html_resource_folders(
                base_path
            )
            if base_path
            else []
        )

        parts = []
        bold_ranges = []
        italic_ranges = []
        images = []

        length = 0

        block_tags = {
            'p',
            'div',
            'section',
            'article',
            'blockquote',
            'li',
            'tr',
            'table',
            'header',
            'footer',
            'main',
            'aside',
            'nav',
            'figure',
            'figcaption',
            'pre',
            'h1',
            'h2',
            'h3',
            'h4',
            'h5',
            'h6'
        }

        bold_tags = {
            'strong',
            'b',
            'h1',
            'h2',
            'h3',
            'h4',
            'h5',
            'h6'
        }

        ignored_tags = {
            'script',
            'style',
            'head',
            'noscript',
            'template',
            'svg'
        }

        def add_break():
            nonlocal length

            if not parts:
                return

            # Нам достаточно посмотреть на последний кусок.
            last = (
                parts[-1]
            )

            if last.endswith(
                '\n\n'
            ):
                return

            if last.endswith(
                '\n'
            ):
                parts.append(
                    '\n'
                )

                length += 1

            else:
                parts.append(
                    '\n\n'
                )

                length += 2

        def append_text(
            value,
            bold=False,
            italic=False
        ):
            nonlocal length

            if not value:
                return

            value = html.unescape(
                value
            )

            value = re.sub(
                r'\s+',
                ' ',
                value
            )

            if not value:
                return

            if (
                parts
                and (
                    parts[-1].endswith(
                        ' '
                    )
                    or parts[-1].endswith(
                        '\n'
                    )
                )
            ):
                value = value.lstrip()

            if not value:
                return

            start = (
                length
            )

            parts.append(
                value
            )

            length += len(
                value
            )

            if bold:
                bold_ranges.append(
                    [
                        start,
                        length
                    ]
                )

            if italic:
                italic_ranges.append(
                    [
                        start,
                        length
                    ]
                )

        def get_embedded_image(
            src
        ):
            if not src:
                return None

            src = html.unescape(
                str(src)
            )

            keys = [
                src,
                src.strip(
                    '<>'
                ),
                Path(
                    src
                    .split(
                        '#',
                        1
                    )[0]
                    .split(
                        '?',
                        1
                    )[0]
                ).name
            ]

            for key in keys:
                image = embedded_resources.get(
                    key
                )

                if image is not None:
                    try:
                        return image.copy()
                    except Exception:
                        pass

            return None

        def load_image(
            src
        ):
            # MHTML resource first.
            image = get_embedded_image(
                src
            )

            if image is not None:
                return image

            # Normal HTML local resource.
            return (
                self.find_local_html_image(
                    src,
                    base_path,
                    resource_folders
                )
            )

        class ReaderHTMLParser(
            HTMLParser
        ):
            def __init__(
                parser_self
            ):
                super().__init__(
                    convert_charrefs=True
                )

                parser_self.bold_depth = 0
                parser_self.italic_depth = 0
                parser_self.ignore_depth = 0

            def handle_starttag(
                parser_self,
                tag,
                attrs
            ):
                nonlocal length

                tag = tag.casefold()

                if tag in ignored_tags:
                    parser_self.ignore_depth += 1
                    return

                if parser_self.ignore_depth:
                    return

                attrs = dict(
                    attrs
                )

                if tag in block_tags:
                    add_break()

                if tag in bold_tags:
                    parser_self.bold_depth += 1

                if tag in (
                    'figcaption',
                    'em',
                    'i'
                ):
                    parser_self.italic_depth += 1

                if tag == 'br':
                    add_break()

                elif tag == 'img':
                    src = (
                        attrs.get(
                            'src'
                        )
                        or ''
                    )

                    image = load_image(
                        src
                    )

                    if image is not None:
                        images.append({
                            'position':
                                length,

                            'image':
                                image,

                            'id':
                                src
                        })

            def handle_startendtag(
                parser_self,
                tag,
                attrs
            ):
                tag_lower = tag.casefold()

                parser_self.handle_starttag(
                    tag,
                    attrs
                )

                if tag_lower not in (
                    'img',
                    'br',
                    'meta',
                    'link',
                    'hr',
                    'input'
                ):
                    parser_self.handle_endtag(
                        tag
                    )

            def handle_endtag(
                parser_self,
                tag
            ):
                tag = tag.casefold()

                if tag in ignored_tags:
                    parser_self.ignore_depth = max(
                        0,
                        parser_self.ignore_depth - 1
                    )

                    return

                if parser_self.ignore_depth:
                    return

                if tag in bold_tags:
                    parser_self.bold_depth = max(
                        0,
                        parser_self.bold_depth - 1
                    )

                if tag in (
                    'figcaption',
                    'em',
                    'i'
                ):
                    parser_self.italic_depth = max(
                        0,
                        parser_self.italic_depth - 1
                    )

                if tag in block_tags:
                    add_break()

            def handle_data(
                parser_self,
                data
            ):
                if parser_self.ignore_depth:
                    return

                append_text(
                    data,
                    parser_self.bold_depth > 0,
                    parser_self.italic_depth > 0
                )

        try:
            parser = ReaderHTMLParser()

            parser.feed(
                content
            )

            parser.close()

        except Exception:
            # Не отдаём исходный HTML Reader'у даже при
            # необычной/битой странице.
            fallback = (
                self.strip_html_for_cache(
                    content
                )
            )

            self.document_bold_ranges = []
            self.document_images = []
            self.document_image_positions = []

            return fallback

        raw = ''.join(
            parts
        )

        left_trim = (
            len(raw)
            - len(
                raw.lstrip()
            )
        )

        result = (
            raw.strip()
        )

        adjusted_bold = []

        for start, end in bold_ranges:
            start -= left_trim
            end -= left_trim

            start = max(
                0,
                start
            )

            end = min(
                len(result),
                end
            )

            if end > start:
                adjusted_bold.append(
                    [
                        start,
                        end
                    ]
                )

        adjusted_italic = []

        for start, end in italic_ranges:
            start -= left_trim
            end -= left_trim

            start = max(
                0,
                start
            )

            end = min(
                len(result),
                end
            )

            if end > start:
                adjusted_italic.append(
                    [
                        start,
                        end
                    ]
                )

        self.document_italic_ranges = (
            self.merge_ranges(
                adjusted_italic
            )
        )

        adjusted_images = []

        for item in images:
            position = (
                item[
                    'position'
                ]
                - left_trim
            )

            position = max(
                0,
                min(
                    position,
                    len(result)
                )
            )

            adjusted_images.append({
                'position':
                    position,

                'image':
                    item[
                        'image'
                    ],

                'id':
                    item[
                        'id'
                    ]
            })

        self.document_bold_ranges = (
            self.merge_ranges(
                adjusted_bold
            )
        )

        self.document_images = sorted(
            adjusted_images,
            key=lambda item:
            item[
                'position'
            ]
        )

        self.document_image_positions = [
            item[
                'position'
            ]
            for item
            in self.document_images
        ]

        return result

    def parse_html_text(
        self,
        content
    ):
        self.timecodes = []
        self.timecode_positions = []

        self.document_bold_ranges = []
        self.document_images = []
        self.document_image_positions = []

        self.reader_title_range = None

        return (
            self.parse_html_document(
                content,
                self.selected_file
            )
        )

    def parse_transmission_text(
        self,
        content
    ):
        self.document_italic_ranges = []
        self.document_bold_ranges = []
        self.document_images = []
        self.document_image_positions = []

        self.reader_title_range = None

        tc_re = re.compile(
            r'#T=(\d{2}:\d{2}:\d{2})'
        )

        first = (
            tc_re.search(
                content
            )
        )

        if first:
            content = (
                content[
                    first.start():
                ]
            )

        clean_parts = []
        timecodes_in_clean = []

        last = 0
        clean_length = 0

        for match in (
            tc_re.finditer(
                content
            )
        ):
            piece = (
                content[
                    last:
                    match.start()
                ]
            )

            clean_parts.append(
                piece
            )

            clean_length += (
                len(
                    piece
                )
            )

            timecodes_in_clean.append(
                (
                    clean_length,
                    match.group(
                        1
                    )
                )
            )

            last = (
                match.end()
            )

        clean_parts.append(
            content[
                last:
            ]
        )

        clean_raw = ''.join(
            clean_parts
        )

        tc_index = 0

        final_parts = []
        final_length = 0

        result_timecodes = []

        raw_pos = 0

        lines = (
            clean_raw.splitlines(
                keepends=True
            )
        )

        if (
            not lines
            and clean_raw
        ):
            lines = [
                clean_raw
            ]

        first_output_line = (
            True
        )

        for raw_line in lines:
            line_body = (
                raw_line.rstrip(
                    '\r\n'
                )
            )

            left_trimmed = (
                line_body.lstrip()
            )

            stripped = (
                left_trimmed.rstrip()
            )

            raw_line_start = (
                raw_pos
            )

            raw_line_end = (
                raw_pos
                + len(
                    raw_line
                )
            )

            if stripped:
                leading = (
                    len(
                        line_body
                    )
                    - len(
                        left_trimmed
                    )
                )

                content_start = (
                    raw_line_start
                    + leading
                )

                content_end = (
                    content_start
                    + len(
                        stripped
                    )
                )

                if not first_output_line:
                    final_parts.append(
                        '\n\n'
                    )

                    final_length += 2

                new_line_start = (
                    final_length
                )

                while (
                    tc_index
                    < len(
                        timecodes_in_clean
                    )
                    and
                    timecodes_in_clean[
                        tc_index
                    ][0]
                    < content_start
                ):
                    result_timecodes.append(
                        (
                            new_line_start,
                            timecodes_in_clean[
                                tc_index
                            ][1]
                        )
                    )

                    tc_index += 1

                while (
                    tc_index
                    < len(
                        timecodes_in_clean
                    )
                    and
                    timecodes_in_clean[
                        tc_index
                    ][0]
                    <= content_end
                ):
                    old_pos, timecode = (
                        timecodes_in_clean[
                            tc_index
                        ]
                    )

                    result_timecodes.append(
                        (
                            new_line_start
                            + max(
                                0,
                                old_pos
                                - content_start
                            ),
                            timecode
                        )
                    )

                    tc_index += 1

                final_parts.append(
                    stripped
                )

                final_length += (
                    len(
                        stripped
                    )
                )

                first_output_line = (
                    False
                )

            raw_pos = (
                raw_line_end
            )

        while (
            tc_index
            < len(
                timecodes_in_clean
            )
        ):
            result_timecodes.append(
                (
                    final_length,
                    timecodes_in_clean[
                        tc_index
                    ][1]
                )
            )

            tc_index += 1

        self.timecodes = (
            result_timecodes
        )

        self.timecode_positions = [
            item[0]
            for item
            in self.timecodes
        ]

        return ''.join(
            final_parts
        )

    # =========================================================
    # END PART 3/4
    # PART 4 STARTS WITH READER CREATE
    # =========================================================
    # =========================================================
    # READER CREATE
    # =========================================================

    def get_reader_cache_key(
        self,
        path
    ):
        path = Path(
            path
        )

        try:
            mtime = (
                path.stat().st_mtime_ns
            )
        except Exception:
            mtime = 0

        return (
            str(path),
            mtime
        )

    def remove_reader_document_cache_for_file(
        self,
        path
    ):
        path_string = str(
            Path(path)
        )

        for key in list(
            self.reader_document_cache.keys()
        ):
            try:
                if key[0] == path_string:
                    self.reader_document_cache.pop(
                        key,
                        None
                    )
            except Exception:
                pass

    def store_current_reader_document_cache(
        self,
        path
    ):
        if not path:
            return

        key = (
            self.get_reader_cache_key(
                path
            )
        )

        # Удаляем старую версию этого же файла.
        self.remove_reader_document_cache_for_file(
            path
        )

        images = []

        for item in self.document_images:
            try:
                images.append({
                    'position':
                        int(
                            item['position']
                        ),

                    'image':
                        item['image'].copy(),

                    'id':
                        item.get(
                            'id',
                            ''
                        )
                })
            except Exception:
                pass

        self.reader_document_cache[
            key
        ] = {
            'text':
                self.reader_content,

            'bold_ranges':
                [
                    list(value)
                    for value
                    in self.document_bold_ranges
                ],

            'italic_ranges':
                [
                    list(value)
                    for value
                    in self.document_italic_ranges
                ],

            'images':
                images,

            'timecodes':
                list(
                    self.timecodes
                ),

            'title_range':
                self.reader_title_range
        }

        # Защита от бесконечного роста RAM.
        if (
            len(
                self.reader_document_cache
            )
            > 30
        ):
            first_key = next(
                iter(
                    self.reader_document_cache
                ),
                None
            )

            if first_key is not None:
                self.reader_document_cache.pop(
                    first_key,
                    None
                )

    def restore_reader_document_cache(
        self,
        path
    ):
        if not path:
            return False

        key = (
            self.get_reader_cache_key(
                path
            )
        )

        entry = (
            self.reader_document_cache.get(
                key
            )
        )

        if not entry:
            return False

        self.reader_content = (
            entry.get(
                'text',
                ''
            )
        )

        self.document_bold_ranges = (
            self.merge_ranges(
                entry.get(
                    'bold_ranges',
                    []
                )
            )
        )

        self.document_italic_ranges = (
            self.merge_ranges(
                entry.get(
                    'italic_ranges',
                    []
                )
            )
        )

        self.document_images = []

        for item in entry.get(
            'images',
            []
        ):
            try:
                self.document_images.append({
                    'position':
                        int(
                            item['position']
                        ),

                    'image':
                        item['image'].copy(),

                    'id':
                        item.get(
                            'id',
                            ''
                        )
                })
            except Exception:
                pass

        self.document_images.sort(
            key=lambda item:
            item['position']
        )

        self.document_image_positions = [
            item['position']
            for item
            in self.document_images
        ]

        self.timecodes = list(
            entry.get(
                'timecodes',
                []
            )
        )

        self.timecode_positions = [
            item[0]
            for item
            in self.timecodes
        ]

        self.reader_title_range = (
            entry.get(
                'title_range'
            )
        )

        return True

    def start_reader_loading_animation(
        self,
        start_percent,
        limit_percent,
        caption
    ):
        self.stop_reader_loading_animation()

        self.reader_loading_animation_value = int(
            start_percent
        )

        self.reader_loading_animation_limit = int(
            limit_percent
        )

        self.reader_loading_animation_caption = (
            caption
        )

        self.show_reader_loading(
            self.reader_loading_animation_value,
            caption
        )

        def tick():
            if not self.reader_loading_frame:
                self.reader_loading_animation_id = None
                return

            value = int(
                getattr(
                    self,
                    'reader_loading_animation_value',
                    start_percent
                )
            )

            limit = int(
                getattr(
                    self,
                    'reader_loading_animation_limit',
                    limit_percent
                )
            )

            if value < limit:
                # Чем дальше, тем медленнее приближаемся
                # к границе этапа.
                distance = (
                    limit - value
                )

                step = max(
                    1,
                    min(
                        3,
                        distance // 8
                        + 1
                    )
                )

                value = min(
                    limit,
                    value + step
                )

                self.reader_loading_animation_value = (
                    value
                )

                self.show_reader_loading(
                    value,
                    self.reader_loading_animation_caption
                )

            self.reader_loading_animation_id = (
                self.root.after(
                    180,
                    tick
                )
            )

        self.reader_loading_animation_id = (
            self.root.after(
                180,
                tick
            )
        )

    def stop_reader_loading_animation(self):
        animation = getattr(
            self,
            'reader_loading_animation_id',
            None
        )

        if animation is not None:
            try:
                self.root.after_cancel(
                    animation
                )
            except Exception:
                pass

        self.reader_loading_animation_id = None

    def show_reader_loading(
        self,
        percent,
        caption='Загрузка'
    ):
        percent = max(
            0,
            min(
                100,
                int(percent)
            )
        )

        if not self.reader_container:
            return

        if not self.reader_loading_frame:
            frame = Frame(
                self.reader_container,
                bg=self.bg_color(),
                height=34
            )

            frame.place(
                relx=0.0,
                rely=1.0,
                x=8,
                y=-38,
                relwidth=1.0,
                width=-16,
                height=30
            )

            canvas = Canvas(
                frame,
                bg=self.bg_color(),
                highlightthickness=0,
                bd=0
            )

            canvas.pack(
                fill=tk.BOTH,
                expand=True
            )

            self.reader_loading_frame = frame
            self.reader_loading_canvas = canvas

        canvas = self.reader_loading_canvas

        try:
            canvas.delete(
                'all'
            )

            canvas.update_idletasks()

            width = max(
                160,
                canvas.winfo_width()
            )

            bar_left = 8

            # Справа отдельная зона только под надпись.
            text_zone_width = 145

            bar_right = max(
                bar_left + 40,
                width
                - text_zone_width
            )

            bar_y = 15

            canvas.create_line(
                bar_left,
                bar_y,
                bar_right,
                bar_y,
                fill=self.line_color(),
                width=5,
                capstyle=tk.ROUND
            )

            done_x = (
                bar_left
                + (
                    bar_right
                    - bar_left
                )
                * (
                    percent / 100.0
                )
            )

            canvas.create_line(
                bar_left,
                bar_y,
                done_x,
                bar_y,
                fill=(
                    self.get_search_current_display_color()
                ),
                width=5,
                capstyle=tk.ROUND
            )

            canvas.create_text(
                width - 8,
                bar_y,
                text=(
                    f'{caption} {percent}%'
                ),
                font=self.status_font,
                fill=self.secondary_color(),
                anchor='e'
            )

            self.reader_loading_frame.lift()
            self.root.update_idletasks()

        except Exception:
            pass

    def hide_reader_loading(self):
        self.stop_reader_loading_animation()

        if self.reader_loading_frame:
            try:
                self.reader_loading_frame.destroy()
            except Exception:
                pass

        self.reader_loading_frame = None
        self.reader_loading_canvas = None
        self.reader_loading_text_item = None
        self.reader_loading_bar_item = None

    def draw_reader_screen(self):
        if (
            not self.selected_file
            or not Path(
                self.selected_file
            ).exists()
        ):
            self.draw_stub_screen(
                10
            )

            return

        self.selected_file = (
            Path(
                self.selected_file
            )
        )

        # Новый документ не наследует состояние перехода
        # через изображения предыдущего документа.
        self._reader_image_start_override = None

        suffix = (
            self.selected_file
            .suffix
            .lower()
        )

        if (
            self.selected_source_type
            not in (
                'book',
                'transmission',
                'project',
                'external'
            )
        ):
            if suffix == '.fb2':
                self.selected_source_type = (
                    'book'
                )
            else:
                self.selected_source_type = (
                    'external'
                )

        self.reader_source_type = (
            self.selected_source_type
        )

        self.reader_is_imam_dialogue = (
            self.reader_source_type
            == 'project'
            and
            self.is_imam_project_file(
                self.selected_file
            )
        )

        self.reader_title_range = None

        # Глобальный поиск не должен менять
        # последние открытые документы.
        if not self.reader_from_global_search:
            if (
                self.reader_source_type
                == 'book'
            ):
                self.last_opened_book = (
                    Path(
                        self.selected_file
                    )
                )

            elif (
                self.reader_source_type
                == 'transmission'
            ):
                self.last_opened_transmission = (
                    Path(
                        self.selected_file
                    )
                )

            elif (
                self.reader_source_type
                == 'project'
            ):
                self.last_opened_project = (
                    Path(
                        self.selected_file
                    )
                )

            elif (
                self.reader_source_type
                == 'external'
            ):
                self.last_opened_external = (
                    Path(
                        self.selected_file
                    )
                )

            self.save_settings()

        self.update_window_title()

        self.canvas.pack_forget()

        self.reader_container = Frame(
            self.middle_frame,
            bg=self.bg_color(),
            highlightthickness=0,
            bd=0
        )

        self.reader_container.pack(
            side=tk.LEFT,
            fill=tk.BOTH,
            expand=True
        )

        cache_entry = (
            self.document_cache.get(
                str(
                    self.selected_file
                )
            )
        )

        parsed_cache_hit = (
            self.restore_reader_document_cache(
                self.selected_file
            )
        )

        if not parsed_cache_hit:
            # Показываем индикатор только там, где разбор
            # действительно может быть тяжёлым.
            if suffix in (
                '.html',
                '.htm',
                '.mhtml',
                '.mht'
            ):
                self.show_reader_loading(
                    5,
                    'Загрузка'
                )

            try:
                content = (
                    self.read_text_file(
                        self.selected_file
                    )
                )

            except Exception as error:
                content = (
                    'Ошибка загрузки файла: '
                    f'{error}'
                )

            if suffix in (
                '.html',
                '.htm',
                '.mhtml',
                '.mht'
            ):
                self.show_reader_loading(
                    15,
                    'Чтение'
                )

            if suffix == '.fb2':
                self.reader_content = (
                    self.parse_fb2_text(
                        content
                    )
                )

            elif suffix == '.md':
                self.reader_content = (
                    self.parse_markdown_text(
                        content
                    )
                )

            elif suffix in (
                '.html',
                '.htm'
            ):
                self.show_reader_loading(
                    25,
                    'Подготовка HTML'
                )

                # Удаляем тяжёлые script/head заранее.
                content = (
                    self.prepare_html_for_reader(
                        content
                    )
                )

                self.show_reader_loading(
                    35,
                    'Разбор HTML'
                )

                self.reader_content = (
                    self.parse_html_text(
                        content
                    )
                )

                self.show_reader_loading(
                    90,
                    'Подготовка страницы'
                )

            elif suffix in (
                '.mhtml',
                '.mht'
            ):
                self.show_reader_loading(
                    40,
                    'MHTML'
                )

                (
                    mhtml_content,
                    mhtml_resources
                ) = self.load_mhtml_document(
                    self.selected_file
                )

                self.show_reader_loading(
                    65,
                    'MHTML'
                )

                self.timecodes = []
                self.timecode_positions = []
                self.reader_title_range = None

                self.reader_content = (
                    self.parse_html_document(
                        mhtml_content,
                        self.selected_file,
                        mhtml_resources
                    )
                )

                self.show_reader_loading(
                    85,
                    'MHTML'
                )

            elif (
                self.reader_source_type
                == 'transmission'
            ):
                self.reader_content = (
                    self.parse_transmission_text(
                        content
                    )
                )

            else:
                self.timecodes = []
                self.timecode_positions = []

                self.document_bold_ranges = []
                self.document_images = []
                self.document_image_positions = []

                self.reader_title_range = None

                self.reader_content = (
                    cache_entry[
                        'text'
                    ]
                    if cache_entry
                    else content
                )

            # Сохраняем уже разобранное состояние в RAM.
            self.store_current_reader_document_cache(
                self.selected_file
            )

            if suffix in (
                '.html',
                '.htm',
                '.mhtml',
                '.mht'
            ):
                self.show_reader_loading(
                    100,
                    'Готово'
                )

        else:
            # Повторное открытие HTML/MHTML:
            # исходный файл и картинки повторно не парсятся.
            pass

        self.clear_reader_layout_cache()

        self.root.update_idletasks()

        width = (
            self.reader_container
            .winfo_width()
        )

        padding = (
            self.get_reader_side_padding(
                width
            )
        )

        self.text_widget = Text(
            self.reader_container,
            wrap=tk.NONE,
            font=self.reader_font,
            bg=self.bg_color(),
            fg=self.text_color(),
            padx=padding,
            pady=0,
            spacing1=0,
            spacing2=0,
            spacing3=0,
            relief=tk.FLAT,
            highlightthickness=0,
            borderwidth=0,
            cursor='arrow',
            selectbackground='#7a9ab8',
            selectforeground=self.text_color(),
            insertbackground=self.text_color()
        )

        self.text_widget.pack(
            side=tk.LEFT,
            fill=tk.BOTH,
            expand=True,
            padx=(
                (
                    8,
                    75
                )
                if self.reader_two_page_mode
                else (
                    0,
                    0
                )
            ),
            pady=(
                self.READER_TOP_PADDING,
                self.READER_BOTTOM_PADDING
            )
        )

        if self.reader_two_page_mode:
            self.text_widget.configure(
                padx=0
            )

            self.create_second_reader_page()

            self.root.update_idletasks()

            self.layout_two_page_reader()

        self.text_widget.tag_config(
            'speaker',
            font=self.reader_font_bold
        )

        self.text_widget.tag_config(
            'document_bold',
            font=self.reader_font_bold
        )

        self.text_widget.tag_config(
            'title',
            font=self.reader_font_bold
        )

        self.text_widget.tag_config(
            'document_italic',
            font=self.reader_font_italic
        )

        self.text_widget.tag_config(
            'highlight',
            background=(
                self.get_reader_highlight_color()
            )
        )

        self.context_menu = Menu(
            self.text_widget,
            tearoff=0
        )

        self.context_menu.add_command(
            label='Копировать',
            command=self.copy_text
        )

        self.context_menu.add_command(
            label='Перенести в заметки',
            command=(
                self.transfer_reader_selection_to_notes
            )
        )

        self.context_menu.add_command(
            label='Сохранить в PNG',
            command=(
                self.save_reader_selection_as_png
            )
        )

        self.text_widget.bind(
            '<Button-1>',
            self.on_reader_click,
            add='+'
        )

        self.text_widget.bind(
            '<Button-3>',
            self.show_context_menu
        )

        self.text_widget.bind(
            '<Control-Key>',
            self.on_ctrl_key
        )

        self.text_widget.bind(
            '<MouseWheel>',
            self.on_reader_scroll
        )

        self.text_widget.bind(
            '<Button-4>',
            self.on_reader_scroll
        )

        self.text_widget.bind(
            '<Button-5>',
            self.on_reader_scroll
        )

        self.root.bind(
            '<Prior>',
            self.on_reader_page_up
        )

        self.root.bind(
            '<Next>',
            self.on_reader_page_down
        )

        self.root.bind(
            '<Key>',
            self.on_key_press
        )

        self.screen_elements = []
        self.highlight_items = []
        self.hover_areas = []

        self.root.update_idletasks()

        self.refresh_reader_font_cache()
        self.calculate_reader_lines_per_page()

        # -----------------------------------------------------
        # Initial position
        # -----------------------------------------------------

        if (
            self.reader_from_global_search
            and
            self.global_search_target_position
            is not None
        ):
            target_position = int(
                self.global_search_target_position
            )

            wanted_position = (
                self.find_reader_start_for_target_line(
                    target_position,
                    self.SEARCH_TARGET_VISUAL_LINE
                )
            )

        else:
            key = str(
                self.selected_file
            )

            saved = (
                self.reading_positions.get(
                    key,
                    '0'
                )
            )

            try:
                wanted_position = int(
                    saved
                )

            except Exception:
                wanted_position = 0

            target_position = None

        if self.reader_content:
            wanted_position = (
                self.normalize_slider_target(
                    wanted_position
                )
            )
        else:
            wanted_position = 0

        self.reader_back_history = []
        self.reader_forward_history = []

        self.show_reader_page_from_position(
            wanted_position,
            silent_save=True
        )

        # -----------------------------------------------------
        # Global search -> local search
        # -----------------------------------------------------

        if (
            self.reader_from_global_search
            and
            len(
                self.search_query
            ) >= self.SEARCH_MIN_CHARS
        ):
            self.search_active = True

            self.rebuild_search_matches(
                preferred_position=(
                    target_position
                ),
                reposition=False
            )

            self.build_overlay()

            if self.search_entry:
                self.search_entry.focus_set()

                self.search_entry.icursor(
                    tk.END
                )

    # =========================================================
    # READER LAYOUT
    # =========================================================

        # Убираем индикатор после первой реальной отрисовки.
        self.root.after_idle(
            self.hide_reader_loading
        )


    def clear_reader_layout_cache(self):
        self.reader_page_cache = {}

        self.measure_cache_normal = {}
        self.measure_cache_bold = {}

        self.reader_current_lines = []
        self.reader_display_map = []

    def refresh_reader_font_cache(self):
        self.reader_normal_tkfont = (
            tkfont.Font(
                family=self.content_font_family,
                size=self.reader_font_size
            )
        )

        self.reader_bold_tkfont = (
            tkfont.Font(
                family=self.content_font_family,
                size=self.reader_font_size,
                weight='bold'
            )
        )

        self.reader_italic_tkfont = (
            tkfont.Font(
                family=self.content_font_family,
                size=self.reader_font_size,
                slant='italic'
            )
        )

        self.measure_cache_normal = {}
        self.measure_cache_bold = {}

    def configure_reader_text_widget(
        self,
        widget
    ):
        widget.tag_config(
            'speaker',
            font=self.reader_font_bold
        )

        widget.tag_config(
            'document_bold',
            font=self.reader_font_bold
        )

        widget.tag_config(
            'title',
            font=self.reader_font_bold
        )

        widget.tag_config(
            'document_italic',
            font=self.reader_font_italic
        )

        widget.tag_config(
            'highlight',
            background=(
                self.get_reader_highlight_color()
            )
        )

    def get_two_page_geometry(self):
        if not self.reader_container:
            return (
                8,
                100,
                300
            )

        try:
            width = max(
                1,
                self.reader_container.winfo_width()
            )
        except Exception:
            width = max(
                1,
                self.root.winfo_width()
            )

        outer = 8
        gap = 100

        available = max(
            100,
            width
            - outer * 2
            - gap
        )

        page_width = max(
            50,
            available // 2
        )

        return (
            outer,
            gap,
            page_width
        )

    def layout_two_page_reader(self):
        if (
            not self.reader_two_page_mode
            or not self.reader_container
            or not self.text_widget
            or not self.second_text_widget
        ):
            return

        outer, gap, page_width = (
            self.get_two_page_geometry()
        )

        try:
            height = max(
                1,
                self.reader_container.winfo_height()
            )

            top = (
                self.READER_TOP_PADDING
            )

            bottom = (
                self.READER_BOTTOM_PADDING
            )

            content_height = max(
                1,
                height
                - top
                - bottom
            )

            left_x = outer

            right_x = (
                outer
                + page_width
                + gap
            )

            # place() используется намеренно:
            # pack(expand=True) при resize мог отдавать
            # колонкам разную ширину.
            self.text_widget.pack_forget()
            self.second_text_widget.pack_forget()

            self.text_widget.place(
                x=left_x,
                y=top,
                width=page_width,
                height=content_height
            )

            self.second_text_widget.place(
                x=right_x,
                y=top,
                width=page_width,
                height=content_height
            )

            self.text_widget.configure(
                padx=0
            )

            self.second_text_widget.configure(
                padx=0
            )

        except Exception:
            pass

    def create_second_reader_page(self):
        if (
            not self.reader_two_page_mode
            or not self.reader_container
            or self.second_text_widget
        ):
            return

        self.second_text_widget = Text(
            self.reader_container,
            wrap=tk.NONE,
            font=self.reader_font,
            bg=self.bg_color(),
            fg=self.text_color(),
            padx=0,
            pady=0,
            spacing1=0,
            spacing2=0,
            spacing3=0,
            relief=tk.FLAT,
            highlightthickness=0,
            borderwidth=0,
            cursor='arrow',
            selectbackground='#7a9ab8',
            selectforeground=self.text_color(),
            insertbackground=self.text_color()
        )

        self.configure_reader_text_widget(
            self.second_text_widget
        )

        self.second_text_widget.bind(
            '<MouseWheel>',
            self.on_reader_scroll
        )

        self.second_text_widget.bind(
            '<Button-4>',
            self.on_reader_scroll
        )

        self.second_text_widget.bind(
            '<Button-5>',
            self.on_reader_scroll
        )

        self.layout_two_page_reader()

    def toggle_reader_two_page_mode(self):
        if (
            self.current_screen
            != 'reader'
            or not self.text_widget
        ):
            return

        preserve = (
            self.reader_page_start
        )

        self.reader_two_page_mode = (
            not self.reader_two_page_mode
        )

        if self.reader_two_page_mode:
            self.text_widget.pack_forget()

            self.create_second_reader_page()

            self.root.update_idletasks()

            self.layout_two_page_reader()

        else:
            try:
                self.text_widget.place_forget()
            except Exception:
                pass

            if self.second_text_widget:
                try:
                    self.second_text_widget.place_forget()
                except Exception:
                    pass

                try:
                    self.second_text_widget.destroy()
                except Exception:
                    pass

            self.second_text_widget = None
            self.reader_second_page = None
            self.reader_second_display_map = []
            self.reader_second_page_photo_images = []

            width = (
                self.reader_container.winfo_width()
            )

            self.text_widget.configure(
                padx=(
                    self.get_reader_side_padding(
                        width
                    )
                )
            )

            self.text_widget.pack(
                side=tk.LEFT,
                fill=tk.BOTH,
                expand=True,
                pady=(
                    self.READER_TOP_PADDING,
                    self.READER_BOTTOM_PADDING
                )
            )

        self.root.update_idletasks()

        self.refresh_reader_font_cache()
        self.calculate_reader_lines_per_page()
        self.clear_reader_layout_cache()

        self.reader_back_history = []
        self.reader_forward_history = []

        self.show_reader_page_from_position(
            preserve,
            silent_save=True
        )

    def toggle_reader_width_mode(self):
        if (
            self.current_screen != 'reader'
            or not self.text_widget
        ):
            return

        preserve = (
            self.reader_page_start
        )

        self.reader_narrow_mode = (
            not self.reader_narrow_mode
        )

        width = (
            self.reader_container.winfo_width()
            if self.reader_container
            else self.root.winfo_width()
        )

        padding = (
            0
            if self.reader_two_page_mode
            else
            self.get_reader_side_padding(
                width
            )
        )

        self.text_widget.configure(
            padx=padding
        )

        if (
            self.reader_two_page_mode
            and self.second_text_widget
        ):
            self.second_text_widget.configure(
                padx=0
            )

        self.root.update_idletasks()

        self.refresh_reader_font_cache()
        self.calculate_reader_lines_per_page()
        self.clear_reader_layout_cache()

        self.reader_back_history = []
        self.reader_forward_history = []

        self.show_reader_page_from_position(
            preserve,
            silent_save=True
        )

        self.save_settings()

    def get_reader_side_padding(
        self,
        width
    ):
        if not self.reader_narrow_mode:
            return (
                self.READER_HORIZONTAL_PADDING_MIN
            )

        if (
            width
            > self.reader_text_max_width
        ):
            return max(
                self.READER_HORIZONTAL_PADDING_MIN,
                (
                    width
                    - self.reader_text_max_width
                ) // 2
            )

        return (
            self.READER_HORIZONTAL_PADDING_MIN
        )

    def get_reader_available_width(self):
        if not self.text_widget:
            return 500

        try:
            width = max(
                1,
                self.text_widget.winfo_width()
            )
        except Exception:
            width = 500

        try:
            padding = int(
                float(
                    self.text_widget.cget(
                        'padx'
                    )
                )
            )

        except Exception:
            padding = 0

        return max(
            50,
            width
            - padding * 2
            - 8
        )

    def get_reader_line_height(self):
        if (
            self.reader_normal_tkfont
            is None
        ):
            self.refresh_reader_font_cache()

        return max(
            self.reader_normal_tkfont.metrics(
                'linespace'
            ),
            self.reader_bold_tkfont.metrics(
                'linespace'
            )
        )

    def calculate_reader_lines_per_page(self):
        if not self.text_widget:
            self.reader_lines_per_page = 1

            return

        height = (
            self.text_widget.winfo_height()
        )

        line_height = (
            self.get_reader_line_height()
        )

        usable = max(
            line_height,
            height
            - self.READER_BOTTOM_SAFETY
        )

        pitch = (
            line_height
            + self.READER_MIN_GAP
        )

        self.reader_lines_per_page = max(
            1,
            int(
                usable // pitch
            )
        )

    # =========================================================
    # DOCUMENT BOLD / MEASURE
    # =========================================================

    def get_bold_subranges(
        self,
        start,
        end
    ):
        result = []

        for a, b in (
            self.document_bold_ranges
        ):
            if b <= start:
                continue

            if a >= end:
                break

            left = max(
                start,
                a
            )

            right = min(
                end,
                b
            )

            if right > left:
                result.append(
                    (
                        left,
                        right
                    )
                )

        return result

    def measure_piece(
        self,
        text,
        bold=False
    ):
        if not text:
            return 0

        cache = (
            self.measure_cache_bold
            if bold
            else self.measure_cache_normal
        )

        value = (
            cache.get(
                text
            )
        )

        if value is not None:
            return value

        font = (
            self.reader_bold_tkfont
            if bold
            else self.reader_normal_tkfont
        )

        value = (
            font.measure(
                text
            )
        )

        if len(cache) < 10000:
            cache[
                text
            ] = value

        return value

    def get_speaker_range_for_paragraph(
        self,
        paragraph_start,
        paragraph_end
    ):
        if (
            self.reader_source_type
            == 'transmission'
        ):
            sample = (
                self.reader_content[
                    paragraph_start:
                    min(
                        paragraph_end,
                        paragraph_start + 200
                    )
                ]
            )

            match = re.match(
                r'^([А-Яа-яЁёA-Za-z\s]+):\s',
                sample
            )

            if match:
                return (
                    paragraph_start,

                    paragraph_start
                    + len(
                        match.group(
                            1
                        )
                    )
                    + 1
                )

        return (
            paragraph_start,
            paragraph_start
        )

    def is_position_bold(
        self,
        position,
        speaker_start,
        speaker_end
    ):
        if (
            speaker_start
            <= position
            < speaker_end
        ):
            return True

        for start, end in (
            self.document_bold_ranges
        ):
            if end <= position:
                continue

            if start > position:
                break

            return (
                start
                <= position
                < end
            )

        return False

    def measure_document_range(
        self,
        start,
        end,
        speaker_start,
        speaker_end
    ):
        if end <= start:
            return 0

        points = {
            start,
            end
        }

        if (
            start
            < speaker_start
            < end
        ):
            points.add(
                speaker_start
            )

        if (
            start
            < speaker_end
            < end
        ):
            points.add(
                speaker_end
            )

        for a, b in (
            self.document_bold_ranges
        ):
            if b <= start:
                continue

            if a >= end:
                break

            points.add(
                max(
                    start,
                    a
                )
            )

            points.add(
                min(
                    end,
                    b
                )
            )

        ordered = sorted(
            points
        )

        width = 0

        for index in range(
            len(
                ordered
            ) - 1
        ):
            a = (
                ordered[
                    index
                ]
            )

            b = (
                ordered[
                    index + 1
                ]
            )

            if b <= a:
                continue

            bold = (
                self.is_position_bold(
                    a,
                    speaker_start,
                    speaker_end
                )
            )

            width += (
                self.measure_piece(
                    self.reader_content[
                        a:b
                    ],
                    bold
                )
            )

        return width

    # =========================================================
    # VISUAL LINE
    # =========================================================

    def build_one_visual_line(
        self,
        position,
        max_width
    ):
        text = (
            self.reader_content
        )

        n = (
            len(
                text
            )
        )

        if position >= n:
            return None

        if (
            text[
                position
            ] == '\n'
        ):
            return {
                'kind':
                    'text',

                'start':
                    position,

                'end':
                    position + 1,

                'visible_end':
                    position,

                'text':
                    ''
            }

        while (
            position < n
            and text[
                position
            ] in ' \t'
        ):
            position += 1

        if position >= n:
            return None

        if (
            text[
                position
            ] == '\n'
        ):
            return {
                'kind':
                    'text',

                'start':
                    position,

                'end':
                    position + 1,

                'visible_end':
                    position,

                'text':
                    ''
            }

        paragraph_start = (
            text.rfind(
                '\n',
                0,
                position
            )
            + 1
        )

        paragraph_end = (
            text.find(
                '\n',
                position
            )
        )

        if paragraph_end < 0:
            paragraph_end = n

        speaker_start, speaker_end = (
            self.get_speaker_range_for_paragraph(
                paragraph_start,
                paragraph_end
            )
        )

        lo = (
            position + 1
        )

        hi = (
            paragraph_end
        )

        best = (
            position + 1
        )

        while lo <= hi:
            mid = (
                lo + hi
            ) // 2

            width = (
                self.measure_document_range(
                    position,
                    mid,
                    speaker_start,
                    speaker_end
                )
            )

            if width <= max_width:
                best = mid
                lo = (
                    mid + 1
                )

            else:
                hi = (
                    mid - 1
                )

        if best >= paragraph_end:
            end = (
                paragraph_end
            )

            if (
                paragraph_end < n
                and text[
                    paragraph_end
                ] == '\n'
            ):
                end = (
                    paragraph_end + 1
                )

            visible_text = (
                text[
                    position:
                    paragraph_end
                ].rstrip(
                    ' \t'
                )
            )

            return {
                'kind':
                    'text',

                'start':
                    position,

                'end':
                    end,

                'visible_end':
                    position
                    + len(
                        visible_text
                    ),

                'text':
                    visible_text
            }

        cut = (
            best
        )

        while (
            cut > position
            and not text[
                cut - 1
            ].isspace()
        ):
            cut -= 1

        if cut <= position:
            cut = (
                best
            )

        next_position = (
            cut
        )

        while (
            next_position
            < paragraph_end
            and text[
                next_position
            ] in ' \t'
        ):
            next_position += 1

        visible_end = (
            cut
        )

        while (
            visible_end > position
            and text[
                visible_end - 1
            ] in ' \t'
        ):
            visible_end -= 1

        return {
            'kind':
                'text',

            'start':
                position,

            'end':
                next_position,

            'visible_end':
                visible_end,

            'text':
                text[
                    position:
                    visible_end
                ]
        }

    # =========================================================
    # IMAGE SIZE
    # =========================================================

    def calculate_display_image_size(
        self,
        image
    ):
        max_width = max(
            20,
            self.get_reader_available_width()
            - 4
        )

        height = (
            self.text_widget.winfo_height()
            if self.text_widget
            else 600
        )

        # Разрешаем картинке занимать почти всю страницу.
        max_height = max(
            20,
            height
            - self.READER_BOTTOM_SAFETY
            - 12
        )

        width, image_height = (
            image.size
        )

        if (
            width <= 0
            or image_height <= 0
        ):
            return (
                1,
                1
            )

        ratio = min(
            1.0,
            max_width
            / float(width),
            max_height
            / float(image_height)
        )

        return (
            max(
                1,
                int(
                    width * ratio
                )
            ),
            max(
                1,
                int(
                    image_height * ratio
                )
            )
        )

    def normalize_page_start(
        self,
        position
    ):
        n = (
            len(
                self.reader_content
            )
        )

        position = max(
            0,
            min(
                int(
                    position
                ),
                n
            )
        )

        while (
            position < n
            and self.reader_content[
                position
            ] in '\r\n'
        ):
            position += 1

        return position

    def build_page_from_position(
        self,
        start,
        image_cursor=None
    ):
        start = (
            self.normalize_page_start(
                start
            )
        )

        if image_cursor is None:
            image_cursor = (
                bisect.bisect_left(
                    self.document_image_positions,
                    start
                )
            )

        image_cursor = max(
            0,
            min(
                int(
                    image_cursor
                ),
                len(
                    self.document_images
                )
            )
        )

        max_width = (
            self.get_reader_available_width()
        )

        widget_height = (
            self.text_widget.winfo_height()
            if self.text_widget
            else 600
        )

        cache_key = (
            start,
            image_cursor,
            int(max_width),
            int(widget_height)
        )

        cached = (
            self.reader_page_cache.get(
                cache_key
            )
        )

        if cached is not None:
            return cached

        line_height = (
            self.get_reader_line_height()
        )

        pitch = (
            line_height
            + self.READER_MIN_GAP
        )

        usable_height = max(
            line_height,
            widget_height
            - self.READER_BOTTOM_SAFETY
        )

        items = []

        position = start

        n = len(
            self.reader_content
        )

        used_height = 0

        current_image_index = (
            image_cursor
        )

        safety = 0

        while (
            (
                position < n
                or current_image_index
                < len(
                    self.document_images
                )
            )
            and used_height < usable_height
            and safety < 10000
        ):
            safety += 1

            # -------------------------------------------------
            # Image at/before current text position.
            # -------------------------------------------------

            if (
                current_image_index
                < len(
                    self.document_images
                )
            ):
                image_data = (
                    self.document_images[
                        current_image_index
                    ]
                )

                image_position = int(
                    image_data[
                        'position'
                    ]
                )

                if image_position <= position:
                    display_size = (
                        self.calculate_display_image_size(
                            image_data[
                                'image'
                            ]
                        )
                    )

                    remaining = (
                        usable_height
                        - used_height
                    )

                    # Если на странице уже есть текст/картинка
                    # и новая картинка не помещается —
                    # страница заканчивается ПЕРЕД ней.
                    if (
                        items
                        and (
                            remaining < 30
                            or display_size[1] + 6
                            > remaining
                        )
                    ):
                        break

                    # Если картинка первая на странице —
                    # обязательно уменьшаем и показываем.
                    if (
                        display_size[1] + 6
                        > remaining
                    ):
                        target_height = max(
                            1,
                            remaining - 6
                        )

                        ratio = (
                            target_height
                            / float(
                                max(
                                    1,
                                    display_size[1]
                                )
                            )
                        )

                        display_size = (
                            max(
                                1,
                                int(
                                    display_size[0]
                                    * ratio
                                )
                            ),
                            max(
                                1,
                                int(
                                    display_size[1]
                                    * ratio
                                )
                            )
                        )

                    items.append({
                        'kind':
                            'image',

                        'position':
                            image_position,

                        'image_index':
                            current_image_index,

                        'image_data':
                            image_data,

                        'display_size':
                            display_size
                    })

                    # КРИТИЧНО:
                    # картинка продвигает image_cursor,
                    # даже если text position не изменился.
                    current_image_index += 1

                    used_height += (
                        display_size[1]
                        + 6
                    )

                    if (
                        usable_height
                        - used_height
                        < line_height
                    ):
                        break

                    continue

            # -------------------------------------------------
            # No more text.
            # -------------------------------------------------

            if position >= n:
                break

            # -------------------------------------------------
            # If next image is ahead, text can continue only
            # up to normal visual line boundaries.
            # -------------------------------------------------

            if (
                usable_height
                - used_height
                < line_height
                and items
            ):
                break

            line = (
                self.build_one_visual_line(
                    position,
                    max_width
                )
            )

            if line is None:
                break

            if (
                not items
                and not line[
                    'text'
                ].strip()
            ):
                new_position = (
                    line[
                        'end'
                    ]
                )

                if new_position <= position:
                    new_position = min(
                        n,
                        position + 1
                    )

                position = (
                    new_position
                )

                continue

            items.append(
                line
            )

            used_height += pitch

            new_position = (
                line[
                    'end'
                ]
            )

            if new_position <= position:
                new_position = min(
                    n,
                    position + 1
                )

            position = (
                new_position
            )

        page = {
            'start':
                start,

            'end':
                position,

            'image_cursor_start':
                image_cursor,

            'image_cursor_end':
                current_image_index,

            'lines':
                items,

            'used_height':
                used_height
        }

        if (
            len(
                self.reader_page_cache
            )
            > 600
        ):
            self.reader_page_cache.clear()

        self.reader_page_cache[
            cache_key
        ] = page

        return page

    def estimate_previous_page_start(
        self,
        current_start
    ):
        if current_start <= 0:
            return 0

        text = (
            self.reader_content
        )

        chars_back = max(
            4000,
            self.reader_lines_per_page
            * 500
        )

        chunk_start = max(
            0,
            current_start
            - chars_back
        )

        while (
            chunk_start > 0
            and not text[
                chunk_start - 1
            ].isspace()
        ):
            chunk_start -= 1

        max_width = (
            self.get_reader_available_width()
        )

        starts = []

        position = (
            self.normalize_page_start(
                chunk_start
            )
        )

        safety = 0

        while (
            position < current_start
            and safety < 10000
        ):
            safety += 1

            line = (
                self.build_one_visual_line(
                    position,
                    max_width
                )
            )

            if line is None:
                break

            if (
                line[
                    'text'
                ].strip()
            ):
                starts.append(
                    line[
                        'start'
                    ]
                )

            new_position = (
                line[
                    'end'
                ]
            )

            if (
                new_position
                <= position
            ):
                new_position = (
                    position + 1
                )

            position = (
                new_position
            )

        if not starts:
            return 0

        index = max(
            0,
            len(
                starts
            )
            - self.reader_lines_per_page
        )

        return (
            starts[
                index
            ]
        )

    def is_last_reader_page(
        self,
        page
    ):
        position = (
            page[
                'end'
            ]
        )

        n = (
            len(
                self.reader_content
            )
        )

        while (
            position < n
            and self.reader_content[
                position
            ] in '\r\n \t'
        ):
            position += 1

        return (
            position >= n
        )

    def get_page_spacing(
        self,
        page
    ):
        text_items = [
            item
            for item
            in page[
                'lines'
            ]
            if item.get(
                'kind',
                'text'
            ) == 'text'
        ]

        count = (
            len(
                text_items
            )
        )

        if count <= 1:
            return 0

        if any(
            item.get(
                'kind'
            ) == 'image'
            for item
            in page[
                'lines'
            ]
        ):
            return (
                self.READER_MIN_GAP
            )

        if (
            self.is_last_reader_page(
                page
            )
        ):
            return (
                self.READER_LAST_PAGE_GAP
            )

        line_height = (
            self.get_reader_line_height()
        )

        height = (
            self.text_widget.winfo_height()
        )

        usable = max(
            line_height,
            height
            - self.READER_BOTTOM_SAFETY
        )

        free = (
            usable
            - count
            * line_height
        )

        return max(
            0,
            int(
                free
                / (
                    count - 1
                )
            )
        )

    # =========================================================
    # SHOW PAGE
    # =========================================================

    def show_reader_page_from_position(
        self,
        start,
        silent_save=False,
        image_cursor=None
    ):
        if not self.text_widget:
            return

        start = (
            self.normalize_page_start(
                start
            )
        )

        if image_cursor is None:
            image_cursor = (
                bisect.bisect_left(
                    self.document_image_positions,
                    start
                )
            )

        page = (
            self.build_page_from_position(
                start,
                image_cursor
            )
        )

        self.reader_page_start = (
            page['start']
        )

        self.reader_page_end = (
            page['end']
        )

        self.reader_page_image_cursor_start = (
            page.get(
                'image_cursor_start',
                image_cursor
            )
        )

        self.reader_page_image_cursor_end = (
            page.get(
                'image_cursor_end',
                image_cursor
            )
        )

        self.reader_image_cursor = (
            self.reader_page_image_cursor_start
        )

        self.reader_current_lines = (
            page['lines']
        )

        self.render_reader_page(
            page
        )

        # -----------------------------------------------------
        # Two page.
        # -----------------------------------------------------

        self.reader_second_page = None

        if (
            self.reader_two_page_mode
            and self.second_text_widget
        ):
            second_start = (
                self.normalize_page_start(
                    page['end']
                )
            )

            second_image_cursor = (
                page.get(
                    'image_cursor_end',
                    image_cursor
                )
            )

            has_second_state = (
                second_start
                < len(
                    self.reader_content
                )
                or second_image_cursor
                < len(
                    self.document_images
                )
            )

            if has_second_state:
                primary_widget = (
                    self.text_widget
                )

                # Строим правую страницу по её ширине.
                self.text_widget = (
                    self.second_text_widget
                )

                try:
                    second_page = (
                        self.build_page_from_position(
                            second_start,
                            second_image_cursor
                        )
                    )
                finally:
                    self.text_widget = (
                        primary_widget
                    )

                self.reader_second_page = (
                    second_page
                )

                primary_map = (
                    self.reader_display_map
                )

                primary_lines = (
                    self.reader_current_lines
                )

                primary_photos = (
                    self.reader_page_photo_images
                )

                try:
                    self.text_widget = (
                        self.second_text_widget
                    )

                    self.reader_display_map = []
                    self.reader_current_lines = (
                        second_page[
                            'lines'
                        ]
                    )

                    self.reader_page_photo_images = []

                    self.render_reader_page(
                        second_page
                    )

                    self.reader_second_display_map = (
                        self.reader_display_map
                    )

                    self.reader_second_page_photo_images = (
                        self.reader_page_photo_images
                    )

                finally:
                    self.text_widget = (
                        primary_widget
                    )

                    self.reader_display_map = (
                        primary_map
                    )

                    self.reader_current_lines = (
                        primary_lines
                    )

                    self.reader_page_photo_images = (
                        primary_photos
                    )

                self.reader_page_end = (
                    second_page[
                        'end'
                    ]
                )

            else:
                try:
                    self.second_text_widget.config(
                        state=tk.NORMAL
                    )

                    self.second_text_widget.delete(
                        '1.0',
                        tk.END
                    )

                    self.second_text_widget.config(
                        state=tk.DISABLED
                    )
                except Exception:
                    pass

        if (
            self.reader_source_type
            == 'transmission'
        ):
            self.current_timecode = (
                self.find_timecode_for_document_position(
                    self.reader_page_start
                )
            )

        else:
            self.current_timecode = (
                '00:00:00'
            )

        self.update_bottom_status()
        self.build_overlay()

        if (
            not silent_save
            and not self.suppress_reader_position_save
        ):
            self.schedule_save_position()

    def add_document_bold_to_line(
        self,
        widget_start,
        document_start,
        document_end
    ):
        for start, end in (
            self.get_bold_subranges(
                document_start,
                document_end
            )
        ):
            self.text_widget.tag_add(
                'document_bold',

                (
                    f'{widget_start}'
                    f' + '
                    f'{start - document_start}'
                    f' chars'
                ),

                (
                    f'{widget_start}'
                    f' + '
                    f'{end - document_start}'
                    f' chars'
                )
            )

    def add_title_to_line(
        self,
        widget_start,
        document_start,
        document_end
    ):
        if not self.reader_title_range:
            return

        title_start, title_end = (
            self.reader_title_range
        )

        a = max(
            title_start,
            document_start
        )

        b = min(
            title_end,
            document_end
        )

        if b <= a:
            return

        self.text_widget.tag_add(
            'title',

            (
                f'{widget_start}'
                f' + '
                f'{a - document_start}'
                f' chars'
            ),

            (
                f'{widget_start}'
                f' + '
                f'{b - document_start}'
                f' chars'
            )
        )

    def prepare_reader_display_line(
        self,
        item
    ):
        value = item.get(
            'text',
            ''
        )

        document_start = item.get(
            'start',
            0
        )

        normal_map = [
            document_start + index
            for index in range(
                len(value)
            )
        ]

        if (
            not self.content_full_justify
            or not value.strip()
            or ' ' not in value
        ):
            return (
                value,
                normal_map
            )

        # Do not stretch the last line of a paragraph.
        end = item.get(
            'end',
            item.get(
                'visible_end',
                document_start
            )
        )

        visible_end = item.get(
            'visible_end',
            document_start
        )

        trailer = (
            self.reader_content[
                visible_end:end
            ]
        )

        if '\n' in trailer:
            return (
                value,
                normal_map
            )

        paragraph_end = self.reader_content.find(
            '\n',
            document_start
        )

        if paragraph_end < 0:
            paragraph_end = len(
                self.reader_content
            )

        # If this line already reaches paragraph end it is
        # the final paragraph line.
        if visible_end >= paragraph_end:
            return (
                value,
                normal_map
            )

        max_width = (
            self.get_reader_available_width()
        )

        speaker_start, speaker_end = (
            self.get_speaker_range_for_paragraph(
                self.reader_content.rfind(
                    '\n',
                    0,
                    document_start
                ) + 1,
                paragraph_end
            )
        )

        current_width = (
            self.measure_document_range(
                document_start,
                visible_end,
                speaker_start,
                speaker_end
            )
        )

        extra_pixels = (
            max_width
            - current_width
        )

        if extra_pixels <= 0:
            return (
                value,
                normal_map
            )

        space_width = max(
            1,
            self.reader_normal_tkfont.measure(
                ' '
            )
        )

        extra_spaces = int(
            extra_pixels
            // space_width
        )

        gaps = [
            index
            for index, char
            in enumerate(value)
            if (
                char == ' '
                and (
                    index == 0
                    or value[
                        index - 1
                    ] != ' '
                )
            )
        ]

        if (
            not gaps
            or extra_spaces <= 0
        ):
            return (
                value,
                normal_map
            )

        base = (
            extra_spaces
            // len(gaps)
        )

        remainder = (
            extra_spaces
            % len(gaps)
        )

        gap_set = set(
            gaps
        )

        output = []
        mapping = []

        gap_number = 0

        for index, char in enumerate(
            value
        ):
            output.append(
                char
            )

            mapping.append(
                document_start
                + index
            )

            if index in gap_set:
                count = (
                    base
                    + (
                        1
                        if gap_number
                        < remainder
                        else 0
                    )
                )

                if count:
                    output.append(
                        ' ' * count
                    )

                    mapping.extend(
                        [None] * count
                    )

                gap_number += 1

        return (
            ''.join(output),
            mapping
        )

    def add_reader_tag_from_document_ranges(
        self,
        tag,
        ranges
    ):
        if not ranges:
            return

        active = False
        start_offset = None

        for index, position in enumerate(
            self.reader_display_map
        ):
            hit = False

            if position is not None:
                for a, b in ranges:
                    if b <= position:
                        continue

                    if a > position:
                        break

                    if a <= position < b:
                        hit = True

                    break

            if hit and not active:
                active = True
                start_offset = index

            elif (
                not hit
                and active
            ):
                self.text_widget.tag_add(
                    tag,
                    f'1.0 + {start_offset} chars',
                    f'1.0 + {index} chars'
                )

                active = False
                start_offset = None

        if active:
            self.text_widget.tag_add(
                tag,
                f'1.0 + {start_offset} chars',
                (
                    '1.0 + '
                    f'{len(self.reader_display_map)} chars'
                )
            )

    def render_reader_page(
        self,
        page
    ):
        items = (
            page[
                'lines'
            ]
        )

        spacing = (
            self.get_page_spacing(
                page
            )
        )

        self.text_widget.config(
            state=tk.NORMAL,
            bg=self.bg_color(),
            fg=self.text_color(),
            selectforeground=self.text_color(),
            spacing1=0,
            spacing2=0,
            spacing3=spacing
        )

        self.text_widget.tag_config(
            'speaker',
            font=self.reader_font_bold
        )

        self.text_widget.tag_config(
            'document_bold',
            font=self.reader_font_bold
        )

        self.text_widget.tag_config(
            'title',
            font=self.reader_font_bold
        )

        self.text_widget.tag_config(
            'document_italic',
            font=self.reader_font_italic
        )

        self.text_widget.tag_config(
            'highlight',
            background=(
                self.get_reader_highlight_color()
            )
        )

        self.text_widget.tag_config(
            'search_match',
            background=(
                self.get_search_normal_display_color()
            )
        )

        self.text_widget.tag_config(
            'search_current',
            background=(
                self.get_search_current_display_color()
            )
        )

        self.text_widget.delete(
            '1.0',
            tk.END
        )

        self.reader_page_photo_images = []
        self.reader_display_map = []

        line_display_data = []

        first_item = (
            True
        )

        for item in items:
            kind = (
                item.get(
                    'kind',
                    'text'
                )
            )

            if not first_item:
                self.text_widget.insert(
                    tk.END,
                    '\n'
                )

                self.reader_display_map.append(
                    None
                )

            first_item = (
                False
            )

            if kind == 'image':
                try:
                    source = (
                        item[
                            'image_data'
                        ][
                            'image'
                        ]
                    )

                    image = source.resize(
                        item[
                            'display_size'
                        ],
                        Image.LANCZOS
                    )

                    photo = (
                        ImageTk.PhotoImage(
                            image
                        )
                    )

                    self.reader_page_photo_images.append(
                        photo
                    )

                    self.text_widget.image_create(
                        tk.END,
                        image=photo,
                        align='center'
                    )

                    self.reader_display_map.append(
                        None
                    )

                except Exception:
                    pass

                continue

            original_visible_text = (
                item[
                    'text'
                ]
            )

            (
                visible_text,
                display_mapping
            ) = self.prepare_reader_display_line(
                item
            )

            widget_start = (
                self.text_widget.index(
                    'end-1c'
                )
            )

            self.text_widget.insert(
                tk.END,
                visible_text
            )

            document_start = (
                item[
                    'start'
                ]
            )

            document_end = (
                item[
                    'visible_end'
                ]
            )

            line_display_data.append({
                'widget_start':
                    widget_start,

                'document_start':
                    document_start,

                'document_end':
                    document_end
            })

            self.add_document_bold_to_line(
                widget_start,
                document_start,
                document_end
            )

            self.add_title_to_line(
                widget_start,
                document_start,
                document_end
            )

            if (
                self.reader_source_type
                == 'transmission'
            ):
                paragraph_start = (
                    self.reader_content.rfind(
                        '\n',
                        0,
                        document_start
                    )
                    + 1
                )

                paragraph_end = (
                    self.reader_content.find(
                        '\n',
                        document_start
                    )
                )

                if paragraph_end < 0:
                    paragraph_end = (
                        len(
                            self.reader_content
                        )
                    )

                speaker_start, speaker_end = (
                    self.get_speaker_range_for_paragraph(
                        paragraph_start,
                        paragraph_end
                    )
                )

                a = max(
                    speaker_start,
                    document_start
                )

                b = min(
                    speaker_end,
                    document_end
                )

                if b > a:
                    self.text_widget.tag_add(
                        'speaker',

                        (
                            f'{widget_start}'
                            f' + '
                            f'{a - document_start}'
                            f' chars'
                        ),

                        (
                            f'{widget_start}'
                            f' + '
                            f'{b - document_start}'
                            f' chars'
                        )
                    )

            self.reader_display_map.extend(
                display_mapping
            )

        if self.content_full_justify:
            # Direct line offsets above were calculated for the
            # source text. Rebuild all document-position tags
            # against reader_display_map.

            for tag_name in (
                'speaker',
                'document_bold',
                'document_italic',
                'title',
                'highlight',
                'search_match',
                'search_current'
            ):
                self.text_widget.tag_remove(
                    tag_name,
                    '1.0',
                    tk.END
                )

            self.add_reader_tag_from_document_ranges(
                'document_bold',
                self.document_bold_ranges
            )

            self.add_reader_tag_from_document_ranges(
                'document_italic',
                self.document_italic_ranges
            )

            if self.reader_title_range:
                self.add_reader_tag_from_document_ranges(
                    'title',
                    [
                        self.reader_title_range
                    ]
                )

            speaker_ranges = []

            if self.reader_source_type == 'transmission':
                paragraph_starts = set()

                for line in self.reader_current_lines:
                    if line.get(
                        'kind',
                        'text'
                    ) != 'text':
                        continue

                    start = line.get(
                        'start',
                        0
                    )

                    paragraph_start = (
                        self.reader_content.rfind(
                            '\n',
                            0,
                            start
                        )
                        + 1
                    )

                    if paragraph_start in paragraph_starts:
                        continue

                    paragraph_starts.add(
                        paragraph_start
                    )

                    paragraph_end = (
                        self.reader_content.find(
                            '\n',
                            paragraph_start
                        )
                    )

                    if paragraph_end < 0:
                        paragraph_end = len(
                            self.reader_content
                        )

                    a, b = (
                        self.get_speaker_range_for_paragraph(
                            paragraph_start,
                            paragraph_end
                        )
                    )

                    if b > a:
                        speaker_ranges.append(
                            [a, b]
                        )

            self.add_reader_tag_from_document_ranges(
                'speaker',
                speaker_ranges
            )

            self.add_reader_tag_from_document_ranges(
                'highlight',
                self.get_current_highlights()
            )

            normal_matches = []
            current_matches = []

            if (
                self.search_active
                and len(
                    self.search_query
                ) >= self.SEARCH_MIN_CHARS
            ):
                for index, value in enumerate(
                    self.search_matches
                ):
                    if index == self.search_current_index:
                        current_matches.append(
                            value
                        )
                    else:
                        normal_matches.append(
                            value
                        )

            self.add_reader_tag_from_document_ranges(
                'search_match',
                normal_matches
            )

            self.add_reader_tag_from_document_ranges(
                'search_current',
                current_matches
            )

        else:
            # HTML figcaption/em/i.
            for line in line_display_data:
                doc_start = line[
                    'document_start'
                ]

                doc_end = line[
                    'document_end'
                ]

                widget_start = line[
                    'widget_start'
                ]

                for a, b in self.document_italic_ranges:
                    if b <= doc_start:
                        continue

                    if a >= doc_end:
                        break

                    left = max(
                        a,
                        doc_start
                    )

                    right = min(
                        b,
                        doc_end
                    )

                    if right > left:
                        self.text_widget.tag_add(
                            'document_italic',
                            (
                                f'{widget_start}'
                                f' + '
                                f'{left - doc_start}'
                                f' chars'
                            ),
                            (
                                f'{widget_start}'
                                f' + '
                                f'{right - doc_start}'
                                f' chars'
                            )
                        )

            self.apply_saved_highlights_to_page(
                line_display_data
            )

            self.apply_search_highlights_to_page(
                line_display_data
            )

        try:
            self.text_widget.tag_raise(
                'highlight'
            )

            self.text_widget.tag_raise(
                'search_match'
            )

            self.text_widget.tag_raise(
                'search_current'
            )

            self.text_widget.tag_raise(
                'document_italic'
            )

            self.text_widget.tag_raise(
                'document_bold'
            )

            self.text_widget.tag_raise(
                'speaker'
            )

            self.text_widget.tag_raise(
                'title'
            )

        except Exception:
            pass

        self.text_widget.config(
            state=tk.DISABLED
        )

        self.text_widget.yview_moveto(
            0.0
        )

    # =========================================================
    # SAVED HIGHLIGHTS
    # =========================================================

    def subtract_range(
        self,
        ranges,
        remove_start,
        remove_end
    ):
        result = []

        for start, end in ranges:
            if (
                end <= remove_start
                or start >= remove_end
            ):
                result.append(
                    [
                        start,
                        end
                    ]
                )

                continue

            if start < remove_start:
                result.append(
                    [
                        start,
                        remove_start
                    ]
                )

            if end > remove_end:
                result.append(
                    [
                        remove_end,
                        end
                    ]
                )

        return result

    def range_is_fully_highlighted(
        self,
        ranges,
        start,
        end
    ):
        if end <= start:
            return False

        cursor = (
            start
        )

        for a, b in ranges:
            if b <= cursor:
                continue

            if a > cursor:
                return False

            cursor = max(
                cursor,
                b
            )

            if cursor >= end:
                return True

        return False

    def current_file_key(self):
        if not self.selected_file:
            return None

        return str(
            self.selected_file
        )

    def get_current_highlights(self):
        key = (
            self.current_file_key()
        )

        if not key:
            return []

        result = []

        for item in (
            self.highlights.get(
                key,
                []
            )
        ):
            try:
                start = int(
                    item[0]
                )

                end = int(
                    item[1]
                )

            except Exception:
                continue

            if end > start:
                result.append(
                    [
                        start,
                        end
                    ]
                )

        return result

    def set_current_highlights(
        self,
        ranges
    ):
        key = (
            self.current_file_key()
        )

        if not key:
            return

        ranges = (
            self.merge_ranges(
                ranges
            )
        )

        if ranges:
            self.highlights[
                key
            ] = ranges

        else:
            self.highlights.pop(
                key,
                None
            )

    def apply_saved_highlights_to_page(
        self,
        line_display_data
    ):
        ranges = (
            self.get_current_highlights()
        )

        if not ranges:
            return

        for line in line_display_data:
            doc_start = (
                line[
                    'document_start'
                ]
            )

            doc_end = (
                line[
                    'document_end'
                ]
            )

            widget_start = (
                line[
                    'widget_start'
                ]
            )

            for start, end in ranges:
                if end <= doc_start:
                    continue

                if start >= doc_end:
                    break

                a = max(
                    start,
                    doc_start
                )

                b = min(
                    end,
                    doc_end
                )

                if b <= a:
                    continue

                self.text_widget.tag_add(
                    'highlight',

                    (
                        f'{widget_start}'
                        f' + '
                        f'{a - doc_start}'
                        f' chars'
                    ),

                    (
                        f'{widget_start}'
                        f' + '
                        f'{b - doc_start}'
                        f' chars'
                    )
                )

    def widget_index_to_offset(
        self,
        index
    ):
        try:
            value = (
                self.text_widget.count(
                    '1.0',
                    index,
                    'chars'
                )
            )

            if value:
                return int(
                    value[0]
                )

        except Exception:
            pass

        return 0

    def get_selected_document_ranges(self):
        if not self.text_widget:
            return []

        try:
            start_index = (
                self.text_widget.index(
                    tk.SEL_FIRST
                )
            )

            end_index = (
                self.text_widget.index(
                    tk.SEL_LAST
                )
            )

        except tk.TclError:
            return []

        start_offset = (
            self.widget_index_to_offset(
                start_index
            )
        )

        end_offset = (
            self.widget_index_to_offset(
                end_index
            )
        )

        upper = min(
            end_offset,
            len(
                self.reader_display_map
            )
        )

        positions = []

        for index in range(
            max(
                0,
                start_offset
            ),
            upper
        ):
            value = (
                self.reader_display_map[
                    index
                ]
            )

            if value is not None:
                positions.append(
                    value
                )

        if not positions:
            return []

        result = []

        start = (
            positions[
                0
            ]
        )

        previous = (
            positions[
                0
            ]
        )

        for position in (
            positions[
                1:
            ]
        ):
            if (
                position
                == previous + 1
            ):
                previous = position

                continue

            if (
                position
                > previous + 1
                and
                self.reader_content[
                    previous + 1:
                    position
                ].isspace()
            ):
                previous = position

                continue

            result.append(
                [
                    start,
                    previous + 1
                ]
            )

            start = (
                position
            )

            previous = (
                position
            )

        result.append(
            [
                start,
                previous + 1
            ]
        )

        return result

    def toggle_selection_highlight(self):
        selected = (
            self.get_selected_document_ranges()
        )

        if not selected:
            return

        saved = (
            self.get_current_highlights()
        )

        fully = all(
            self.range_is_fully_highlighted(
                saved,
                start,
                end
            )
            for start, end
            in selected
        )

        if fully:
            for start, end in selected:
                saved = (
                    self.subtract_range(
                        saved,
                        start,
                        end
                    )
                )

        else:
            saved.extend(
                selected
            )

            saved = (
                self.merge_ranges(
                    saved
                )
            )

        self.set_current_highlights(
            saved
        )

        self.save_settings()

        self.render_reader_page({
            'start':
                self.reader_page_start,

            'end':
                self.reader_page_end,

            'lines':
                self.reader_current_lines
        })

    def delete_all_highlights(self):
        key = (
            self.current_file_key()
        )

        if not key:
            return

        self.highlights.pop(
            key,
            None
        )

        self.save_settings()

        if self.text_widget:
            self.render_reader_page({
                'start':
                    self.reader_page_start,

                'end':
                    self.reader_page_end,

                'lines':
                    self.reader_current_lines
            })

    # =========================================================
    # SEARCH HIGHLIGHTS / SEARCH UI
    # =========================================================

    def apply_search_highlights_to_page(
        self,
        line_display_data
    ):
        if (
            not self.search_active
            or len(
                self.search_query
            ) < self.SEARCH_MIN_CHARS
            or not self.search_matches
        ):
            return

        for match_index, (
            match_start,
            match_end
        ) in enumerate(
            self.search_matches
        ):
            tag = (
                'search_current'
                if (
                    match_index
                    == self.search_current_index
                )
                else 'search_match'
            )

            for line in (
                line_display_data
            ):
                doc_start = (
                    line[
                        'document_start'
                    ]
                )

                doc_end = (
                    line[
                        'document_end'
                    ]
                )

                if match_end <= doc_start:
                    continue

                if match_start >= doc_end:
                    continue

                a = max(
                    match_start,
                    doc_start
                )

                b = min(
                    match_end,
                    doc_end
                )

                if b <= a:
                    continue

                widget_start = (
                    line[
                        'widget_start'
                    ]
                )

                self.text_widget.tag_add(
                    tag,

                    (
                        f'{widget_start}'
                        f' + '
                        f'{a - doc_start}'
                        f' chars'
                    ),

                    (
                        f'{widget_start}'
                        f' + '
                        f'{b - doc_start}'
                        f' chars'
                    )
                )

    def open_search(self):
        if (
            self.current_screen
            != 'reader'
            or self.search_active
        ):
            return

        self.search_active = (
            True
        )

        self.build_overlay()

        if self.search_entry:
            self.search_entry.focus_set()

            self.search_entry.icursor(
                tk.END
            )

    def close_search(self):
        if not self.search_active:
            return

        self.search_active = False

        self.search_matches = []
        self.search_current_index = -1
        self.search_query = ''

        if self.search_entry:
            try:
                self.search_entry.destroy()

            except Exception:
                pass

            self.search_entry = None

        if self.text_widget:
            self.render_reader_page({
                'start':
                    self.reader_page_start,

                'end':
                    self.reader_page_end,

                'lines':
                    self.reader_current_lines
            })

        self.build_overlay()

    def create_search_overlay(
        self,
        geometry
    ):
        if not geometry:
            return

        center_x = (
            geometry[
                'center_x'
            ]
        )

        center_y = (
            self.SEARCH_BOX_TOP
            + self.SEARCH_BOX_HEIGHT
            // 2
        )

        box_left = (
            geometry[
                'left'
            ]
        )

        box_right = (
            geometry[
                'right'
            ]
        )

        box_width = (
            geometry[
                'width'
            ]
        )

        image_key = (
            geometry[
                'image_key'
            ]
        )

        self.search_box_item = (
            self.top_canvas.create_image(
                center_x,
                center_y,
                image=self.photo_frames[
                    image_key
                ][10],
                anchor='center'
            )
        )

        if image_key == '34':
            counter_width = 45

            entry_width = max(
                28,
                box_width
                - self.SEARCH_TEXT_LEFT
                - counter_width
                - 8
            )

            counter_x = (
                box_right - 8
            )

        else:
            counter_width = 75

            entry_width = max(
                50,
                box_width
                - self.SEARCH_TEXT_LEFT
                - counter_width
                - self.SEARCH_TEXT_RIGHT
            )

            counter_x = (
                box_right
                - self.SEARCH_TEXT_RIGHT
            )

        self.search_entry = tk.Entry(
            self.top_canvas,
            font=(
                'Alice',
                12
            ),
            bd=0,
            relief=tk.FLAT,
            highlightthickness=0,
            bg=self.bg_color(),
            fg=self.text_color(),
            insertbackground=self.text_color()
        )

        self.search_entry.insert(
            0,
            self.search_query
        )

        self.search_entry.place(
            x=(
                box_left
                + self.SEARCH_TEXT_LEFT
            ),
            y=(
                self.SEARCH_BOX_TOP
                + 4
            ),
            width=entry_width,
            height=22
        )

        self.search_entry.bind(
            '<KeyRelease>',
            self.on_search_key_release
        )

        self.search_entry.bind(
            '<Return>',
            lambda event:
            self.search_next()
        )

        self.search_entry.bind(
            '<Shift-Return>',
            lambda event:
            self.search_previous()
        )

        self.search_entry.bind(
            '<Escape>',
            lambda event:
            self.close_search()
        )

        self.search_entry.bind(
            '<Control-KeyPress>',
            self.on_reader_search_ctrl_key
        )

        self.search_entry.bind(
            '<Button-3>',
            self.show_search_context_menu
        )

        self.search_count_item = (
            self.top_canvas.create_text(
                counter_x,
                center_y,
                text=(
                    self.get_search_counter_text()
                ),
                font=(
                    'Alice',
                    11
                ),
                fill=self.secondary_color(),
                anchor='e'
            )
        )

        self.add_overlay_button(
            self.top_canvas,
            '31',
            geometry[
                'x31'
            ],
            self.TOP_ICON_Y,
            self.search_previous
        )

        self.add_overlay_button(
            self.top_canvas,
            '32',
            geometry[
                'x32'
            ],
            self.TOP_ICON_Y,
            self.search_next
        )

        self.add_overlay_button(
            self.top_canvas,
            '33',
            geometry[
                'x33'
            ],
            self.TOP_ICON_Y,
            self.close_search
        )

    def on_reader_search_ctrl_key(
        self,
        event
    ):
        code = getattr(
            event,
            'keycode',
            None
        )

        char = (
            getattr(
                event,
                'char',
                ''
            ) or ''
        ).lower()

        if code == 65 or char in ('a', 'ф'):
            entry = self.search_entry

            if entry:
                def select_all():
                    try:
                        if (
                            self.search_entry
                            is entry
                            and entry.winfo_exists()
                        ):
                            entry.focus_set()

                            entry.selection_range(
                                0,
                                tk.END
                            )

                            entry.icursor(
                                tk.END
                            )
                    except Exception:
                        pass

                self.root.after_idle(
                    select_all
                )

            return 'break'

        if code == 86 or char in ('v', 'м'):
            return self.paste_into_search(
                event
            )

        if code == 67 or char in ('c', 'с'):
            try:
                self.search_entry.event_generate(
                    '<<Copy>>'
                )
            except Exception:
                pass

            return 'break'

        if code == 88 or char in ('x', 'ч'):
            try:
                self.search_entry.event_generate(
                    '<<Cut>>'
                )

                self.root.after_idle(
                    self.on_search_key_release
                )
            except Exception:
                pass

            return 'break'

    def paste_into_search(
        self,
        event=None
    ):
        if not self.search_entry:
            return 'break'

        try:
            value = (
                self.root.clipboard_get()
            )

        except tk.TclError:
            return 'break'

        try:
            if (
                self.search_entry.selection_present()
            ):
                self.search_entry.delete(
                    tk.SEL_FIRST,
                    tk.SEL_LAST
                )

        except Exception:
            pass

        position = (
            self.search_entry.index(
                tk.INSERT
            )
        )

        self.search_entry.insert(
            position,
            value
        )

        self.search_query = (
            self.search_entry.get()
        )

        self.rebuild_search_matches()

        return 'break'

    def show_search_context_menu(
        self,
        event
    ):
        self.search_context_menu = Menu(
            self.search_entry,
            tearoff=0
        )

        self.search_context_menu.add_command(
            label='Вставить',
            command=self.paste_into_search
        )

        try:
            self.search_context_menu.tk_popup(
                event.x_root,
                event.y_root
            )

        finally:
            self.search_context_menu.grab_release()

        return 'break'

    def get_search_counter_text(self):
        if (
            len(
                self.search_query
            ) < self.SEARCH_MIN_CHARS
        ):
            return ''

        total = (
            len(
                self.search_matches
            )
        )

        if total == 0:
            return '0/0'

        current = (
            self.search_current_index
            + 1
            if self.search_current_index
            >= 0
            else 1
        )

        return (
            f'{current}/{total}'
        )

    def update_search_counter(self):
        if (
            self.search_count_item
            is None
        ):
            return

        try:
            self.top_canvas.itemconfig(
                self.search_count_item,
                text=(
                    self.get_search_counter_text()
                ),
                fill=self.secondary_color()
            )

        except Exception:
            pass

    def on_search_key_release(
        self,
        event=None
    ):
        if not self.search_entry:
            return

        if event is not None:
            keycode = getattr(
                event,
                'keycode',
                None
            )

            state = getattr(
                event,
                'state',
                0
            )

            # Ctrl+A.
            #
            # Windows virtual-key A = 65 независимо от
            # EN/RU раскладки. Ничего не перестраиваем,
            # иначе build_overlay уничтожит Entry и
            # выделение немедленно пропадёт.
            if (
                keycode == 65
                and (
                    state & 0x0004
                )
            ):
                return 'break'

            if event.keysym in (
                'Control_L',
                'Control_R',
                'Return',
                'Shift_L',
                'Shift_R',
                'Left',
                'Right',
                'Up',
                'Down',
                'Home',
                'End'
            ):
                return

        value = (
            self.search_entry.get()
        )

        # Если содержимое вообще не изменилось,
        # нет причины пересоздавать search overlay.
        if value == self.search_query:
            return

        self.search_query = value

        self.rebuild_search_matches()

    def rebuild_search_matches(
        self,
        preferred_position=None,
        reposition=True
    ):
        self.search_matches = []
        self.search_current_index = -1

        if (
            len(
                self.search_query.strip()
            )
            >= self.SEARCH_MIN_CHARS
        ):
            self.search_matches = (
                self.find_query_matches(
                    self.reader_content,
                    self.search_query
                )
            )

        if self.search_matches:
            starts = [
                item[0]
                for item
                in self.search_matches
            ]

            if preferred_position is not None:
                index = bisect.bisect_left(
                    starts,
                    preferred_position
                )

                if index >= len(starts):
                    index = len(starts) - 1

                if (
                    index > 0
                    and abs(
                        starts[index - 1]
                        - preferred_position
                    )
                    <= abs(
                        starts[index]
                        - preferred_position
                    )
                ):
                    index -= 1

            else:
                index = bisect.bisect_left(
                    starts,
                    self.reader_page_start
                )

                if index >= len(starts):
                    index = 0

            self.search_current_index = (
                index
            )

            target = (
                self.search_matches[
                    index
                ][0]
            )

            if reposition:
                self.show_search_match_with_context(
                    target
                )

            else:
                self.render_reader_page({
                    'start':
                        self.reader_page_start,

                    'end':
                        self.reader_page_end,

                    'lines':
                        self.reader_current_lines
                })

                self.build_overlay()

        elif self.text_widget:
            self.render_reader_page({
                'start':
                    self.reader_page_start,

                'end':
                    self.reader_page_end,

                'lines':
                    self.reader_current_lines
            })

            self.build_overlay()

        self.update_search_counter()

        if self.search_entry:
            self.search_entry.focus_set()

    def search_next(self):
        if not self.search_matches:
            return 'break'

        self.search_current_index += 1

        if (
            self.search_current_index
            >= len(
                self.search_matches
            )
        ):
            self.search_current_index = 0

        self.goto_current_search_match()

        return 'break'

    def search_previous(self):
        if not self.search_matches:
            return 'break'

        self.search_current_index -= 1

        if (
            self.search_current_index
            < 0
        ):
            self.search_current_index = (
                len(
                    self.search_matches
                ) - 1
            )

        self.goto_current_search_match()

        return 'break'

    def goto_current_search_match(self):
        if (
            not self.search_matches
            or self.search_current_index < 0
        ):
            return

        start, end = (
            self.search_matches[
                self.search_current_index
            ]
        )

        already_visible = False

        for item in self.reader_current_lines:
            if item.get(
                'kind',
                'text'
            ) != 'text':
                continue

            line_start = item.get(
                'start',
                0
            )

            line_end = item.get(
                'visible_end',
                line_start
            )

            if (
                start < line_end
                and end > line_start
            ):
                already_visible = True
                break

        if already_visible:
            self.render_reader_page({
                'start':
                    self.reader_page_start,

                'end':
                    self.reader_page_end,

                'lines':
                    self.reader_current_lines
            })

            self.build_overlay()

        else:
            self.show_search_match_with_context(
                start
            )

        self.update_search_counter()

        if self.search_entry:
            self.search_entry.focus_set()

    def get_current_bookmarks(self):
        key = (
            self.current_file_key()
        )

        if not key:
            return []

        result = []

        for value in (
            self.bookmarks.get(
                key,
                []
            )
        ):
            try:
                position = int(
                    value
                )

            except Exception:
                continue

            if position >= 0:
                result.append(
                    position
                )

        return sorted(
            set(
                result
            )
        )

    def set_current_bookmarks(
        self,
        values
    ):
        key = (
            self.current_file_key()
        )

        if not key:
            return

        result = []

        for value in values:
            try:
                value = int(
                    value
                )

            except Exception:
                continue

            if value >= 0:
                result.append(
                    value
                )

        result = sorted(
            set(
                result
            )
        )

        if result:
            self.bookmarks[
                key
            ] = result

        else:
            self.bookmarks.pop(
                key,
                None
            )

    def toggle_bookmark(self):
        if not self.reader_content:
            return

        position = (
            self.reader_page_start
        )

        marks = (
            self.get_current_bookmarks()
        )

        index = (
            bisect.bisect_left(
                marks,
                position
            )
        )

        if (
            index < len(
                marks
            )
            and marks[
                index
            ] == position
        ):
            marks.pop(
                index
            )

        else:
            marks.insert(
                index,
                position
            )

        self.set_current_bookmarks(
            marks
        )

        self.save_settings()
        self.build_overlay()

    def goto_previous_bookmark(self):
        marks = (
            self.get_current_bookmarks()
        )

        if not marks:
            return

        index = (
            bisect.bisect_left(
                marks,
                self.reader_page_start
            )
            - 1
        )

        if index < 0:
            return

        self.reader_back_history = []
        self.reader_forward_history = []

        self.show_reader_page_from_position(
            marks[
                index
            ]
        )

    def goto_next_bookmark(self):
        marks = (
            self.get_current_bookmarks()
        )

        if not marks:
            return

        index = (
            bisect.bisect_right(
                marks,
                self.reader_page_start
            )
        )

        if (
            index >= len(
                marks
            )
        ):
            return

        self.reader_back_history = []
        self.reader_forward_history = []

        self.show_reader_page_from_position(
            marks[
                index
            ]
        )

    def create_antialiased_bookmark_marker(
        self,
        size=12
    ):
        scale = 4

        image = Image.new(
            'RGBA',
            (
                size * scale,
                size * scale
            ),
            (
                0,
                0,
                0,
                0
            )
        )

        draw = (
            ImageDraw.Draw(
                image
            )
        )

        rgb = (
            self.hex_to_rgb(
                self.theme_marker_colors.get(
                    self.theme_name,
                    self.HIGHLIGHT_COLOR
                )
            )
        )

        margin = (
            scale
        )

        draw.ellipse(
            (
                margin,
                margin,
                size * scale
                - margin - 1,
                size * scale
                - margin - 1
            ),
            fill=(
                rgb[0],
                rgb[1],
                rgb[2],
                255
            )
        )

        image = image.resize(
            (
                size,
                size
            ),
            Image.LANCZOS
        )

        return (
            ImageTk.PhotoImage(
                image
            )
        )

    def draw_bookmark_markers(
        self,
        x1,
        x2
    ):
        self.bookmark_marker_items = []
        self.bookmark_marker_images = []

        if (
            not self.reader_content
            or x2 <= x1
        ):
            return

        total = float(
            len(
                self.reader_content
            )
        )

        if total <= 0:
            return

        for position in (
            self.get_current_bookmarks()
        ):
            ratio = max(
                0.0,
                min(
                    1.0,
                    position / total
                )
            )

            x = (
                x1
                + ratio
                * (
                    x2 - x1
                )
            )

            photo = (
                self.create_antialiased_bookmark_marker()
            )

            self.bookmark_marker_images.append(
                photo
            )

            item = (
                self.bottom_canvas.create_image(
                    x,
                    self.LINE_Y,
                    image=photo,
                    anchor='center'
                )
            )

            self.bookmark_marker_items.append({
                'item':
                    item,

                'position':
                    position,

                'x':
                    x
            })

    def find_bookmark_marker_at(
        self,
        x,
        y
    ):
        for marker in (
            self.bookmark_marker_items
        ):
            dx = (
                x
                - marker[
                    'x'
                ]
            )

            dy = (
                y
                - self.LINE_Y
            )

            if (
                dx * dx
                + dy * dy
                <= 100
            ):
                return marker

        return None

    def delete_bookmark_position(
        self,
        position
    ):
        marks = [
            value
            for value
            in self.get_current_bookmarks()
            if value != position
        ]

        self.set_current_bookmarks(
            marks
        )

        self.save_settings()
        self.build_overlay()

    def delete_context_bookmark(self):
        if (
            self.context_bookmark_position
            is None
        ):
            return

        self.delete_bookmark_position(
            self.context_bookmark_position
        )

        self.context_bookmark_position = (
            None
        )

    def delete_all_bookmarks(self):
        key = (
            self.current_file_key()
        )

        if not key:
            return

        self.bookmarks.pop(
            key,
            None
        )

        self.save_settings()
        self.build_overlay()

    def get_bottom_button(
        self,
        key
    ):
        for button in (
            self.overlay_buttons
        ):
            if (
                button[
                    'canvas'
                ] is self.bottom_canvas
                and
                button[
                    'key'
                ] == key
            ):
                return button

        return None

    def on_bottom_right_click(
        self,
        event
    ):
        if (
            self.current_screen
            != 'reader'
        ):
            return

        fill = (
            self.get_bottom_button(
                '29'
            )
        )

        if (
            fill
            and abs(
                fill[
                    'x'
                ] - event.x
            ) <= 17
            and abs(
                fill[
                    'y'
                ] - event.y
            ) <= 17
        ):
            if (
                self.fill_icon_menu
                is None
            ):
                self.fill_icon_menu = Menu(
                    self.bottom_canvas,
                    tearoff=0
                )

                self.fill_icon_menu.add_command(
                    label='Удалить все заливки',
                    command=(
                        self.delete_all_highlights
                    )
                )

            try:
                self.fill_icon_menu.tk_popup(
                    event.x_root,
                    event.y_root
                )

            finally:
                self.fill_icon_menu.grab_release()

            return 'break'

        bookmark = (
            self.get_bottom_button(
                '21'
            )
        )

        if (
            bookmark
            and abs(
                bookmark[
                    'x'
                ] - event.x
            ) <= 17
            and abs(
                bookmark[
                    'y'
                ] - event.y
            ) <= 17
        ):
            if (
                self.bookmark_icon_menu
                is None
            ):
                self.bookmark_icon_menu = Menu(
                    self.bottom_canvas,
                    tearoff=0
                )

                self.bookmark_icon_menu.add_command(
                    label='Удалить все закладки',
                    command=(
                        self.delete_all_bookmarks
                    )
                )

            try:
                self.bookmark_icon_menu.tk_popup(
                    event.x_root,
                    event.y_root
                )

            finally:
                self.bookmark_icon_menu.grab_release()

            return 'break'

        marker = (
            self.find_bookmark_marker_at(
                event.x,
                event.y
            )
        )

        if marker is None:
            return

        self.context_bookmark_position = (
            marker[
                'position'
            ]
        )

        if (
            self.bookmark_marker_menu
            is None
        ):
            self.bookmark_marker_menu = Menu(
                self.bottom_canvas,
                tearoff=0
            )

            self.bookmark_marker_menu.add_command(
                label='Удалить',
                command=(
                    self.delete_context_bookmark
                )
            )

        try:
            self.bookmark_marker_menu.tk_popup(
                event.x_root,
                event.y_root
            )

        finally:
            self.bookmark_marker_menu.grab_release()

        return 'break'

    # =========================================================
    # SLIDER / STATUS
    # =========================================================

    def get_reader_line_right(self):
        # Reserve space for percentage and 41.png.
        return (
            self.root.winfo_width()
            - 104
        )

    def get_reader_percentage_x(self):
        return (
            self.root.winfo_width()
            - 48
        )

    def get_reader_width_button_x(self):
        return (
            self.root.winfo_width()
            - 20
        )

    def in_slider_zone(
        self,
        x,
        y
    ):
        if (
            self.current_screen
            != 'reader'
        ):
            return False

        x1 = (
            self.LINE_LEFT
        )

        x2 = (
            self.get_reader_line_right()
        )

        if x2 <= x1:
            return False

        return (
            x1 - 14
            <= x
            <= x2 + 14
            and
            abs(
                y - self.LINE_Y
            ) <= 16
        )

    def on_bottom_press(
        self,
        event
    ):
        index = (
            self.hit_overlay_button(
                self.bottom_canvas,
                event.x,
                event.y
            )
        )

        if index is not None:
            self.press_overlay_button(
                index
            )

            return

        if (
            self.reader_content
            and
            self.in_slider_zone(
                event.x,
                event.y
            )
        ):
            self.is_dragging_runner = (
                True
            )

            self.update_runner_visuals(
                event.x
            )

    def on_bottom_drag(
        self,
        event
    ):
        if self.is_dragging_runner:
            self.update_runner_visuals(
                event.x
            )

    def on_bottom_release(
        self,
        event
    ):
        if not self.is_dragging_runner:
            return

        self.is_dragging_runner = (
            False
        )

        self.commit_slider_jump(
            event.x
        )

    def get_slider_ratio_from_x(
        self,
        x
    ):
        x1 = (
            self.LINE_LEFT
        )

        x2 = (
            self.get_reader_line_right()
        )

        if x2 <= x1:
            return 0.0

        return max(
            0.0,
            min(
                1.0,
                (
                    x - x1
                )
                / float(
                    x2 - x1
                )
            )
        )

    def update_runner_visuals(
        self,
        x
    ):
        ratio = (
            self.get_slider_ratio_from_x(
                x
            )
        )

        x1 = (
            self.LINE_LEFT
        )

        x2 = (
            self.get_reader_line_right()
        )

        if (
            self.runner_item
            is not None
            and x2 > x1
        ):
            self.bottom_canvas.coords(
                self.runner_item,
                x1
                + ratio
                * (
                    x2 - x1
                ),
                self.LINE_Y
            )

        if (
            self.bottom_pct_item
            is not None
        ):
            self.bottom_canvas.itemconfig(
                self.bottom_pct_item,
                text=(
                    f'{int(round(ratio * 100))}%'
                )
            )

    def commit_slider_jump(
        self,
        x
    ):
        if not self.reader_content:
            return

        ratio = (
            self.get_slider_ratio_from_x(
                x
            )
        )

        position = int(
            ratio
            * len(
                self.reader_content
            )
        )

        position = (
            self.normalize_slider_target(
                position
            )
        )

        self.reader_back_history = []
        self.reader_forward_history = []

        image_cursor = (
            bisect.bisect_left(
                self.document_image_positions,
                position
            )
        )

        self.show_reader_page_from_position(
            position,
            image_cursor=image_cursor
        )

    def normalize_slider_target(
        self,
        position
    ):
        text = (
            self.reader_content
        )

        if not text:
            return 0

        n = (
            len(
                text
            )
        )

        position = max(
            0,
            min(
                int(
                    position
                ),
                n - 1
            )
        )

        while (
            position < n
            and text[
                position
            ] in '\r\n'
        ):
            position += 1

        if position >= n:
            return (
                n - 1
            )

        if (
            position > 0
            and not text[
                position - 1
            ].isspace()
            and not text[
                position
            ].isspace()
        ):
            while (
                position > 0
                and not text[
                    position - 1
                ].isspace()
            ):
                position -= 1

        return position

    def get_read_ratio(self):
        if not self.reader_content:
            return 0.0

        return max(
            0.0,
            min(
                1.0,
                self.reader_page_start
                / float(
                    len(
                        self.reader_content
                    )
                )
            )
        )

    def update_bottom_status(self):
        if (
            self.current_screen
            != 'reader'
        ):
            return

        if (
            self.bottom_tc_item
            is not None
        ):
            value = (
                self.current_timecode
                if
                self.reader_source_type
                == 'transmission'
                else ''
            )

            try:
                self.bottom_canvas.itemconfig(
                    self.bottom_tc_item,
                    text=value,
                    fill=self.secondary_color()
                )

            except Exception:
                pass

        ratio = (
            self.get_read_ratio()
        )

        if (
            self.bottom_pct_item
            is not None
        ):
            try:
                self.bottom_canvas.itemconfig(
                    self.bottom_pct_item,
                    text=(
                        f'{int(round(ratio * 100))}%'
                    ),
                    fill=self.secondary_color()
                )

            except Exception:
                pass

        if (
            self.line_item
            is not None
        ):
            try:
                self.bottom_canvas.itemconfig(
                    self.line_item,
                    fill=self.line_color()
                )

            except Exception:
                pass

        if (
            self.runner_item
            is not None
            and not
            self.is_dragging_runner
        ):
            x1 = (
                self.LINE_LEFT
            )

            x2 = (
                self.root.winfo_width()
                - self.LINE_RIGHT_MARGIN
            )

            if x2 > x1:
                try:
                    self.bottom_canvas.coords(
                        self.runner_item,

                        x1
                        + ratio
                        * (
                            x2 - x1
                        ),

                        self.LINE_Y
                    )

                except Exception:
                    pass

    # =========================================================
    # PAGE NAVIGATION / TIMECODE
    # =========================================================

    def prepare_next_reader_page_from(
        self,
        page
    ):
        """
        Подготавливает переход после страницы.

        У изображения нет собственного символа в reader_content,
        поэтому next_image_index хранится отдельно.
        """

        if not page:
            self._reader_image_start_override = None
            return

        end = (
            self.normalize_page_start(
                page.get(
                    'end',
                    0
                )
            )
        )

        next_image_index = page.get(
            'next_image_index'
        )

        if next_image_index is None:
            self._reader_image_start_override = None
            return

        self._reader_image_start_override = (
            end,
            int(
                next_image_index
            )
        )

    def clear_reader_image_navigation_override(
        self
    ):
        self._reader_image_start_override = None

    def scroll_page_down(self):
        if (
            self.current_screen
            != 'reader'
            or not self.reader_content
        ):
            return

        # Состояние, после которого нужно продолжить.
        if (
            self.reader_two_page_mode
            and self.reader_second_page
        ):
            page = (
                self.reader_second_page
            )

        else:
            page = (
                self.build_page_from_position(
                    self.reader_page_start,
                    self.reader_page_image_cursor_start
                )
            )

        next_start = (
            self.normalize_page_start(
                page[
                    'end'
                ]
            )
        )

        next_image_cursor = (
            page.get(
                'image_cursor_end',
                len(
                    self.document_images
                )
            )
        )

        has_more_text = (
            next_start
            < len(
                self.reader_content
            )
        )

        has_more_images = (
            next_image_cursor
            < len(
                self.document_images
            )
        )

        if (
            not has_more_text
            and not has_more_images
        ):
            return

        current_state = (
            self.reader_page_start,
            self.reader_page_image_cursor_start
        )

        self.reader_back_history.append(
            current_state
        )

        self.reader_forward_history = []

        self.show_reader_page_from_position(
            next_start,
            image_cursor=next_image_cursor
        )

    def scroll_page_up(self):
        if (
            self.current_screen
            != 'reader'
        ):
            return

        current_state = (
            self.reader_page_start,
            self.reader_page_image_cursor_start
        )

        if self.reader_back_history:
            previous = (
                self.reader_back_history.pop()
            )

            self.reader_forward_history.append(
                current_state
            )

            if (
                isinstance(
                    previous,
                    (
                        tuple,
                        list
                    )
                )
                and len(previous) >= 2
            ):
                previous_start = int(
                    previous[0]
                )

                previous_image_cursor = int(
                    previous[1]
                )

            else:
                previous_start = int(
                    previous
                )

                previous_image_cursor = (
                    bisect.bisect_left(
                        self.document_image_positions,
                        previous_start
                    )
                )

            self.show_reader_page_from_position(
                previous_start,
                image_cursor=previous_image_cursor
            )

            return

        if self.reader_page_start <= 0:
            return

        previous_start = (
            self.estimate_previous_page_start(
                self.reader_page_start
            )
        )

        previous_image_cursor = (
            bisect.bisect_left(
                self.document_image_positions,
                previous_start
            )
        )

        if (
            previous_start
            >= self.reader_page_start
        ):
            return

        self.show_reader_page_from_position(
            previous_start,
            image_cursor=previous_image_cursor
        )

    def on_reader_scroll(
        self,
        event
    ):
        # Ctrl + wheel changes font size.
        if (
            getattr(
                event,
                'state',
                0
            )
            & 0x0004
        ):
            if (
                getattr(
                    event,
                    'num',
                    None
                ) == 4
                or getattr(
                    event,
                    'delta',
                    0
                ) > 0
            ):
                self.increase_font()

            elif (
                getattr(
                    event,
                    'num',
                    None
                ) == 5
                or getattr(
                    event,
                    'delta',
                    0
                ) < 0
            ):
                self.decrease_font()

            return 'break'

        if (
            getattr(
                event,
                'num',
                None
            ) == 5
            or
            getattr(
                event,
                'delta',
                0
            ) < 0
        ):
            self.scroll_page_down()

        elif (
            getattr(
                event,
                'num',
                None
            ) == 4
            or
            getattr(
                event,
                'delta',
                0
            ) > 0
        ):
            self.scroll_page_up()

        return 'break'

    def on_reader_page_up(
        self,
        event=None
    ):
        if (
            self.current_screen
            == 'reader'
        ):
            self.scroll_page_up()

            return 'break'

    def on_reader_page_down(
        self,
        event=None
    ):
        if (
            self.current_screen
            == 'reader'
        ):
            self.scroll_page_down()

            return 'break'

    def find_timecode_for_document_position(
        self,
        char_index
    ):
        if not self.timecodes:
            return (
                '00:00:00'
            )

        index = (
            bisect.bisect_right(
                self.timecode_positions,
                char_index
            )
            - 1
        )

        if index < 0:
            return (
                '00:00:00'
            )

        return (
            self.timecodes[
                index
            ][1]
        )

    def get_document_position_from_display_offset(
        self,
        offset,
        prefer_right=True
    ):
        if not self.reader_display_map:
            return (
                self.reader_page_start
            )

        offset = max(
            0,
            min(
                offset,
                len(
                    self.reader_display_map
                ) - 1
            )
        )

        value = (
            self.reader_display_map[
                offset
            ]
        )

        if value is not None:
            return value

        if prefer_right:
            for index in range(
                offset + 1,
                len(
                    self.reader_display_map
                )
            ):
                value = (
                    self.reader_display_map[
                        index
                    ]
                )

                if value is not None:
                    return value

        for index in range(
            offset - 1,
            -1,
            -1
        ):
            value = (
                self.reader_display_map[
                    index
                ]
            )

            if value is not None:
                return (
                    value + 1
                )

        return (
            self.reader_page_start
        )

    # =========================================================
    # TRANSMISSION MEDIA
    # =========================================================

    def get_transmission_timecode_at_event(
        self,
        event
    ):
        if (
            not self.text_widget
            or self.reader_source_type
            != 'transmission'
        ):
            return (
                '00:00:00',
                self.reader_page_start
            )

        try:
            index = self.text_widget.index(
                f'@{event.x},{event.y}'
            )

            offset = self.widget_index_to_offset(
                index
            )

            position = (
                self.get_document_position_from_display_offset(
                    offset
                )
            )

        except Exception:
            position = (
                self.reader_page_start
            )

        return (
            self.find_timecode_for_document_position(
                position
            ),
            position
        )

    def media_normalize_text(
        self,
        value
    ):
        value = str(
            value or ''
        ).casefold()

        # Частая транслитерация кириллицы.
        table = {
            'а': 'a',
            'б': 'b',
            'в': 'v',
            'г': 'g',
            'д': 'd',
            'е': 'e',
            'ё': 'e',
            'ж': 'zh',
            'з': 'z',
            'и': 'i',
            'й': 'i',
            'к': 'k',
            'л': 'l',
            'м': 'm',
            'н': 'n',
            'о': 'o',
            'п': 'p',
            'р': 'r',
            'с': 's',
            'т': 't',
            'у': 'u',
            'ф': 'f',
            'х': 'h',
            'ц': 'c',
            'ч': 'ch',
            'ш': 'sh',
            'щ': 'sch',
            'ъ': '',
            'ы': 'y',
            'ь': '',
            'э': 'e',
            'ю': 'yu',
            'я': 'ya'
        }

        value = ''.join(
            table.get(char, char)
            for char in value
        )

        value = unicodedata.normalize(
            'NFKD',
            value
        )

        value = ''.join(
            char
            for char in value
            if not unicodedata.combining(
                char
            )
        )

        value = re.sub(
            r'[^a-z0-9]+',
            ' ',
            value
        )

        return ' '.join(
            value.split()
        )

    def get_transmission_media_signature(self):
        if not self.selected_file:
            return (
                '',
                '',
                set()
            )

        stem = Path(
            self.selected_file
        ).stem

        date_token = ''

        match = re.match(
            r'^(\d{4})-(\d{2})-(\d{2})\s*-\s*(.*)$',
            stem
        )

        if match:
            date_token = (
                match.group(1)
                + match.group(2)
                + match.group(3)
            )

            title = match.group(4)

        else:
            title = stem

        normalized = (
            self.media_normalize_text(
                title
            )
        )

        words = {
            word
            for word in normalized.split()
            if len(word) >= 3
        }

        return (
            normalized,
            date_token,
            words
        )

    def get_media_file_score(
        self,
        path
    ):
        (
            wanted_title,
            wanted_date,
            wanted_words
        ) = (
            self.get_transmission_media_signature()
        )

        candidate_stem = Path(
            path
        ).stem

        candidate = (
            self.media_normalize_text(
                candidate_stem
            )
        )

        candidate_words = {
            word
            for word in candidate.split()
            if len(word) >= 3
        }

        if not wanted_title:
            return 0.0

        sequence = (
            difflib.SequenceMatcher(
                None,
                wanted_title,
                candidate
            ).ratio()
        )

        if wanted_words:
            intersection = (
                wanted_words
                & candidate_words
            )

            word_score = (
                len(intersection)
                / float(
                    len(wanted_words)
                )
            )
        else:
            word_score = 0.0

        containment = 0.0

        if (
            wanted_title in candidate
            or candidate in wanted_title
        ):
            containment = 1.0

        date_score = 0.0

        if wanted_date:
            digits = re.sub(
                r'\D+',
                '',
                candidate_stem
            )

            yyyy = wanted_date[0:4]
            mm = wanted_date[4:6]
            dd = wanted_date[6:8]

            date_variants = (
                yyyy + mm + dd,
                dd + mm + yyyy,
                dd + mm + yyyy[2:],
                yyyy[2:] + mm + dd
            )

            if any(
                value in digits
                for value in date_variants
            ):
                date_score = 1.0

        # Дата имеет высокий вес, но не может полностью
        # перевесить совершенно другое название.
        return (
            word_score * 0.50
            + sequence * 0.25
            + date_score * 0.20
            + containment * 0.05
        )

    def find_best_transmission_media_file(
        self,
        folder,
        kind
    ):
        if not folder:
            return None

        folder = Path(
            folder
        )

        if (
            not folder.exists()
            or not folder.is_dir()
        ):
            return None

        if kind == 'video':
            extensions = {
                '.mp4',
                '.mkv',
                '.avi',
                '.mov',
                '.wmv',
                '.webm',
                '.m4v',
                '.mpeg',
                '.mpg'
            }
        else:
            extensions = {
                '.mp3',
                '.m4a',
                '.aac',
                '.wav',
                '.flac',
                '.ogg',
                '.wma',
                '.opus'
            }

        best_path = None
        best_score = -1.0

        try:
            iterator = folder.rglob(
                '*'
            )

            for path in iterator:
                if (
                    not path.is_file()
                    or path.suffix.casefold()
                    not in extensions
                ):
                    continue

                score = (
                    self.get_media_file_score(
                        path
                    )
                )

                if score > best_score:
                    best_score = score
                    best_path = path

        except Exception:
            return None

        # Если уверенность слишком мала, не открываем
        # случайный файл.
        if best_score < 0.30:
            return None

        return best_path

    def timecode_to_seconds(
        self,
        value
    ):
        try:
            hours, minutes, seconds = (
                str(value).split(
                    ':'
                )
            )

            return (
                int(hours) * 3600
                + int(minutes) * 60
                + int(seconds)
            )

        except Exception:
            return 0

    def get_windows_associated_executable(
        self,
        path
    ):
        if sys.platform != 'win32':
            return None

        try:
            import ctypes
            from ctypes import wintypes

            ASSOCF_NONE = 0
            ASSOCSTR_EXECUTABLE = 2

            extension = Path(
                path
            ).suffix

            if not extension:
                return None

            shlwapi = ctypes.windll.shlwapi

            function = (
                shlwapi.AssocQueryStringW
            )

            function.argtypes = [
                wintypes.DWORD,
                wintypes.DWORD,
                wintypes.LPCWSTR,
                wintypes.LPCWSTR,
                wintypes.LPWSTR,
                ctypes.POINTER(
                    wintypes.DWORD
                )
            ]

            function.restype = (
                wintypes.HRESULT
            )

            length = wintypes.DWORD(
                0
            )

            function(
                ASSOCF_NONE,
                ASSOCSTR_EXECUTABLE,
                extension,
                None,
                None,
                ctypes.byref(
                    length
                )
            )

            if length.value <= 1:
                return None

            buffer = ctypes.create_unicode_buffer(
                length.value
            )

            result = function(
                ASSOCF_NONE,
                ASSOCSTR_EXECUTABLE,
                extension,
                None,
                buffer,
                ctypes.byref(
                    length
                )
            )

            if result != 0:
                return None

            value = buffer.value.strip()

            if value:
                return value

        except Exception:
            pass

        return None

    def find_mpc_hc_executable(
        self,
        associated=None
    ):
        if associated:
            name = Path(
                associated
            ).name.casefold()

            if (
                'mpc-hc' in name
                or 'mpc_hc' in name
                or name in (
                    'mpc-hc.exe',
                    'mpc-hc64.exe'
                )
            ):
                return associated

        candidates = []

        for environment_name in (
            'ProgramFiles',
            'ProgramFiles(x86)',
            'LOCALAPPDATA'
        ):
            root = os.getenv(
                environment_name
            )

            if not root:
                continue

            root = Path(
                root
            )

            candidates.extend([
                root
                / 'MPC-HC'
                / 'mpc-hc64.exe',

                root
                / 'MPC-HC'
                / 'mpc-hc.exe',

                root
                / 'MPC-HC'
                / 'mpc-hc64'
                / 'mpc-hc64.exe',

                root
                / 'MPC-HC'
                / 'mpc-hc'
                / 'mpc-hc.exe'
            ])

        for candidate in candidates:
            try:
                if candidate.exists():
                    return str(
                        candidate
                    )
            except Exception:
                pass

        return None

    def open_media_at_timecode(
        self,
        path,
        timecode
    ):
        path = Path(
            path
        )

        if not path.exists():
            return False

        seconds = (
            self.timecode_to_seconds(
                timecode
            )
        )

        milliseconds = max(
            0,
            int(
                seconds * 1000
            )
        )

        # Нормализуем таймкод для MPC-HC.
        #
        # Передаём именно HH:MM:SS, например:
        #
        # /startpos 00:27:17
        try:
            total_seconds = max(
                0,
                int(seconds)
            )

            hours = (
                total_seconds // 3600
            )

            minutes = (
                (
                    total_seconds
                    % 3600
                )
                // 60
            )

            secs = (
                total_seconds % 60
            )

            mpc_timecode = (
                f'{hours:02d}:'
                f'{minutes:02d}:'
                f'{secs:02d}'
            )

        except Exception:
            mpc_timecode = (
                str(
                    timecode
                )
            )

        if sys.platform == 'win32':
            associated = (
                self.get_windows_associated_executable(
                    path
                )
            )

            associated_lower = (
                str(
                    associated or ''
                ).casefold()
            )

            # ---------------------------------------------
            # MPC-HC
            #
            # Сначала проверяем ассоциированный плеер.
            # Если это не MPC-HC, отдельно ищем
            # установленный MPC-HC.
            #
            # Это важно в том числе для x86-сборки:
            # 32-битный процесс Windows может видеть
            # ассоциации файлов иначе, чем x64.
            # ---------------------------------------------

            mpc = (
                self.find_mpc_hc_executable(
                    associated
                )
            )

            if mpc:
                try:
                    subprocess.Popen(
                        [
                            str(mpc),
                            '/startpos',
                            mpc_timecode,
                            str(path)
                        ],
                        close_fds=True
                    )

                    return True

                except Exception:
                    pass
            # ---------------------------------------------
            # MPC-BE
            # Оставляем тот же формат времени.
            # ---------------------------------------------

            if (
                associated
                and (
                    'mpc-be'
                    in associated_lower
                    or
                    'mpc_be'
                    in associated_lower
                )
            ):
                try:
                    subprocess.Popen(
                        [
                            associated,
                            '/startpos',
                            mpc_timecode,
                            str(path)
                        ],
                        close_fds=True
                    )

                    return True

                except Exception:
                    pass

            # ---------------------------------------------
            # VLC
            # ---------------------------------------------

            if (
                associated
                and
                'vlc'
                in associated_lower
            ):
                try:
                    subprocess.Popen(
                        [
                            associated,
                            '--start-time',
                            str(seconds),
                            str(path)
                        ],
                        close_fds=True
                    )

                    return True

                except Exception:
                    pass

            # ---------------------------------------------
            # PotPlayer
            # ---------------------------------------------

            if (
                associated
                and
                'potplayer'
                in associated_lower
            ):
                try:
                    subprocess.Popen(
                        [
                            associated,
                            str(path),
                            (
                                '/seek='
                                + str(
                                    milliseconds
                                )
                            )
                        ],
                        close_fds=True
                    )

                    return True

                except Exception:
                    pass

            # ---------------------------------------------
            # mpv
            # ---------------------------------------------

            if (
                associated
                and
                'mpv'
                in associated_lower
            ):
                try:
                    subprocess.Popen(
                        [
                            associated,
                            (
                                '--start='
                                + str(seconds)
                            ),
                            str(path)
                        ],
                        close_fds=True
                    )

                    return True

                except Exception:
                    pass

            # Неизвестный плеер.
            try:
                os.startfile(
                    str(path)
                )

                return True

            except Exception:
                return False

        # Non-Windows fallback.
        try:
            subprocess.Popen(
                [
                    'xdg-open',
                    str(path)
                ]
            )

            return True

        except Exception:
            return False

    def open_transmission_media(
        self,
        kind
    ):
        folder = (
            self.video_folder
            if kind == 'video'
            else self.audio_folder
        )

        path = (
            self.find_best_transmission_media_file(
                folder,
                kind
            )
        )

        if path is None:
            try:
                self.root.bell()
            except Exception:
                pass

            return

        self.open_media_at_timecode(
            path,
            self.current_timecode
        )

    def choose_transmission_media_file(
        self
    ):
        initialdir = (
            self.last_media_file_directory
        )

        if (
            not initialdir
            or not Path(
                initialdir
            ).exists()
        ):
            initialdir = (
                self.video_folder
                or self.audio_folder
                or str(
                    self.base_dir
                )
            )

        if not Path(
            initialdir
        ).exists():
            initialdir = str(
                self.base_dir
            )

        filename = (
            filedialog.askopenfilename(
                parent=self.root,
                title='Указать файл',
                initialdir=str(
                    initialdir
                ),
                filetypes=[
                    (
                        'Медиафайлы',
                        (
                            '*.mp4 *.mkv *.avi *.mov *.wmv '
                            '*.webm *.m4v *.mpeg *.mpg '
                            '*.mp3 *.m4a *.aac *.wav *.flac '
                            '*.ogg *.wma *.opus'
                        )
                    ),
                    (
                        'Все файлы',
                        '*.*'
                    )
                ]
            )
        )

        if not filename:
            return

        path = Path(
            filename
        )

        self.last_media_file_directory = (
            path.parent
        )

        self.factory_reset_pending = False
        self.save_settings()

        self.open_media_at_timecode(
            path,
            self.current_timecode
        )

    def show_transmission_media_context_menu(
        self,
        event
    ):
        (
            timecode,
            position
        ) = (
            self.get_transmission_timecode_at_event(
                event
            )
        )

        self.current_timecode = timecode
        self.update_bottom_status()

        menu = Menu(
            self.text_widget,
            tearoff=0
        )

        if self.video_folder:
            menu.add_command(
                label='Открыть Видео',
                command=lambda:
                self.open_transmission_media(
                    'video'
                )
            )

        if self.audio_folder:
            menu.add_command(
                label='Открыть Аудио',
                command=lambda:
                self.open_transmission_media(
                    'audio'
                )
            )

        menu.add_command(
            label='Указать файл',
            command=(
                self.choose_transmission_media_file
            )
        )

        try:
            menu.tk_popup(
                event.x_root,
                event.y_root
            )

        finally:
            menu.grab_release()

        return 'break'

    def on_reader_click(
        self,
        event
    ):
        if (
            not self.text_widget
            or
            self.reader_source_type
            != 'transmission'
        ):
            return

        try:
            index = (
                self.text_widget.index(
                    f'@{event.x},{event.y}'
                )
            )

        except Exception:
            return

        offset = (
            self.widget_index_to_offset(
                index
            )
        )

        position = (
            self.get_document_position_from_display_offset(
                offset
            )
        )

        self.current_timecode = (
            self.find_timecode_for_document_position(
                position
            )
        )

        self.update_bottom_status()

    # =========================================================
    # COPY / CONTEXT MENU
    # =========================================================

    def get_reader_effective_bold_ranges(
        self
    ):
        ranges = [
            list(value)
            for value
            in self.document_bold_ranges
        ]

        if self.reader_title_range:
            ranges.append(
                list(
                    self.reader_title_range
                )
            )

        # Speaker names in transmissions are visually bold.
        if (
            self.reader_source_type
            == 'transmission'
            and self.reader_content
        ):
            position = 0

            for line in self.reader_content.splitlines(
                keepends=True
            ):
                body_end = (
                    position
                    + len(
                        line.rstrip(
                            '\r\n'
                        )
                    )
                )

                a, b = (
                    self.get_speaker_range_for_paragraph(
                        position,
                        body_end
                    )
                )

                if b > a:
                    ranges.append(
                        [
                            a,
                            b
                        ]
                    )

                position += len(line)

        return self.merge_ranges(
            ranges
        )

    def intersect_export_ranges(
        self,
        ranges,
        start,
        end
    ):
        result = []

        for a, b in ranges:
            left = max(
                start,
                a
            )

            right = min(
                end,
                b
            )

            if right > left:
                result.append(
                    (
                        left,
                        right
                    )
                )

        return result

    def build_formatted_export(
        self,
        source_text,
        selected_ranges,
        bold_ranges,
        highlight_ranges,
        mode
    ):
        output = []

        for selection_index, (
            selection_start,
            selection_end
        ) in enumerate(
            selected_ranges
        ):
            points = {
                selection_start,
                selection_end
            }

            for ranges in (
                bold_ranges,
                highlight_ranges
            ):
                for a, b in ranges:
                    if (
                        b <= selection_start
                        or a >= selection_end
                    ):
                        continue

                    points.add(
                        max(
                            a,
                            selection_start
                        )
                    )

                    points.add(
                        min(
                            b,
                            selection_end
                        )
                    )

            ordered = sorted(
                points
            )

            for index in range(
                len(ordered) - 1
            ):
                a = ordered[index]
                b = ordered[index + 1]

                if b <= a:
                    continue

                value = source_text[a:b]

                bold = any(
                    x <= a < y
                    for x, y
                    in bold_ranges
                )

                marked = any(
                    x <= a < y
                    for x, y
                    in highlight_ranges
                )

                if mode == 'html':
                    value = html.escape(
                        value
                    ).replace(
                        '\n',
                        '<br>\n'
                    )

                    if bold:
                        value = (
                            '<strong>'
                            + value
                            + '</strong>'
                        )

                    if marked:
                        color = (
                            self.get_reader_highlight_color()
                        )

                        value = (
                            '<span style="background-color:'
                            + color
                            + ';">'
                            + value
                            + '</span>'
                        )

                else:
                    # Markdown.
                    if bold:
                        value = (
                            '**'
                            + value
                            + '**'
                        )

                    if marked:
                        value = (
                            '<mark>'
                            + value
                            + '</mark>'
                        )

                output.append(
                    value
                )

            if (
                selection_index
                < len(selected_ranges) - 1
            ):
                output.append(
                    '<br>\n'
                    if mode == 'html'
                    else '\n'
                )

        return ''.join(
            output
        )

    def set_windows_html_clipboard(
        self,
        plain_text,
        html_fragment
    ):
        """
        Put CF_UNICODETEXT + CF_HTML on Windows clipboard.
        Word can paste formatting from CF_HTML.
        """

        if sys.platform != 'win32':
            self.root.clipboard_clear()
            self.root.clipboard_append(
                plain_text
            )
            return

        import ctypes

        kernel32 = ctypes.windll.kernel32
        user32 = ctypes.windll.user32

        GMEM_MOVEABLE = 0x0002
        CF_UNICODETEXT = 13

        html_body = (
            '<html><body>'
            '<!--StartFragment-->'
            + html_fragment
            + '<!--EndFragment-->'
            '</body></html>'
        )

        template = (
            'Version:0.9\r\n'
            'StartHTML:{:010d}\r\n'
            'EndHTML:{:010d}\r\n'
            'StartFragment:{:010d}\r\n'
            'EndFragment:{:010d}\r\n'
        )

        empty_header = template.format(
            0,
            0,
            0,
            0
        )

        start_html = len(
            empty_header.encode(
                'utf-8'
            )
        )

        prefix = (
            '<html><body>'
            '<!--StartFragment-->'
        )

        start_fragment = (
            start_html
            + len(
                prefix.encode(
                    'utf-8'
                )
            )
        )

        end_fragment = (
            start_fragment
            + len(
                html_fragment.encode(
                    'utf-8'
                )
            )
        )

        end_html = (
            start_html
            + len(
                html_body.encode(
                    'utf-8'
                )
            )
        )

        header = template.format(
            start_html,
            end_html,
            start_fragment,
            end_fragment
        )

        html_bytes = (
            (
                header
                + html_body
            ).encode(
                'utf-8'
            )
            + b'\x00'
        )

        plain_bytes = (
            plain_text.encode(
                'utf-16-le'
            )
            + b'\x00\x00'
        )

        def allocate(
            data
        ):
            handle = kernel32.GlobalAlloc(
                GMEM_MOVEABLE,
                len(data)
            )

            if not handle:
                raise RuntimeError(
                    'GlobalAlloc failed'
                )

            pointer = kernel32.GlobalLock(
                handle
            )

            if not pointer:
                raise RuntimeError(
                    'GlobalLock failed'
                )

            ctypes.memmove(
                pointer,
                data,
                len(data)
            )

            kernel32.GlobalUnlock(
                handle
            )

            return handle

        hwnd = (
            self.root.winfo_id()
        )

        if not user32.OpenClipboard(
            hwnd
        ):
            raise RuntimeError(
                'OpenClipboard failed'
            )

        try:
            user32.EmptyClipboard()

            plain_handle = allocate(
                plain_bytes
            )

            user32.SetClipboardData(
                CF_UNICODETEXT,
                plain_handle
            )

            cf_html = user32.RegisterClipboardFormatW(
                'HTML Format'
            )

            html_handle = allocate(
                html_bytes
            )

            user32.SetClipboardData(
                cf_html,
                html_handle
            )

        finally:
            user32.CloseClipboard()

    def copy_reader_formatted(
        self,
        mode
    ):
        selected = (
            self.get_selected_document_ranges()
        )

        if not selected:
            return

        plain = ''.join(
            self.reader_content[a:b]
            for a, b
            in selected
        )

        bold = (
            self.get_reader_effective_bold_ranges()
        )

        highlights = (
            self.get_current_highlights()
        )

        if mode == 'html':
            formatted = (
                self.build_formatted_export(
                    self.reader_content,
                    selected,
                    bold,
                    highlights,
                    'html'
                )
            )

            self.set_windows_html_clipboard(
                plain,
                formatted
            )

        else:
            formatted = (
                self.build_formatted_export(
                    self.reader_content,
                    selected,
                    bold,
                    highlights,
                    'markdown'
                )
            )

            self.root.clipboard_clear()
            self.root.clipboard_append(
                formatted
            )

    def copy_notes_formatted(
        self,
        mode
    ):
        selection = (
            self.get_notes_selection()
        )

        if not selection:
            return

        start_index, end_index = (
            selection
        )

        start = self.get_note_text_offset(
            start_index
        )

        end = self.get_note_text_offset(
            end_index
        )

        value = self.notes_text.get(
            '1.0',
            'end-1c'
        )

        selected = [
            (
                start,
                end
            )
        ]

        bold = self.get_note_tag_ranges(
            'note_bold'
        )

        highlights = self.get_note_tag_ranges(
            'note_highlight'
        )

        plain = value[
            start:end
        ]

        if mode == 'html':
            formatted = (
                self.build_formatted_export(
                    value,
                    selected,
                    bold,
                    highlights,
                    'html'
                )
            )

            self.set_windows_html_clipboard(
                plain,
                formatted
            )

        else:
            formatted = (
                self.build_formatted_export(
                    value,
                    selected,
                    bold,
                    highlights,
                    'markdown'
                )
            )

            self.root.clipboard_clear()
            self.root.clipboard_append(
                formatted
            )

    def get_next_screen_png_name(
        self,
        directory
    ):
        directory = Path(
            directory
        )

        number = 1

        while True:
            name = (
                f'Screen_{number:03d}'
            )

            if not (
                directory
                / (
                    name + '.png'
                )
            ).exists():
                return name

            number += 1

    def get_pil_font(
        self,
        family,
        size,
        bold=False
    ):
        candidates = []

        if sys.platform == 'win32':
            windows_fonts = (
                Path(
                    os.environ.get(
                        'WINDIR',
                        r'C:\Windows'
                    )
                )
                / 'Fonts'
            )

            normalized = re.sub(
                r'[^a-z0-9]',
                '',
                family.casefold()
            )

            try:
                for path in windows_fonts.glob(
                    '*.ttf'
                ):
                    stem = re.sub(
                        r'[^a-z0-9]',
                        '',
                        path.stem.casefold()
                    )

                    if normalized in stem:
                        if bold:
                            if (
                                'bold' in stem
                                or stem.endswith('bd')
                            ):
                                candidates.insert(
                                    0,
                                    path
                                )
                            else:
                                candidates.append(
                                    path
                                )
                        else:
                            candidates.append(
                                path
                            )
            except Exception:
                pass

            candidates.extend([
                windows_fonts / (
                    'arialbd.ttf'
                    if bold
                    else 'arial.ttf'
                )
            ])

        for path in candidates:
            try:
                return ImageFont.truetype(
                    str(path),
                    int(size)
                )
            except Exception:
                pass

        try:
            return ImageFont.truetype(
                'arialbd.ttf'
                if bold
                else 'arial.ttf',
                int(size)
            )
        except Exception:
            return ImageFont.load_default()

    def save_text_as_png(
        self,
        text,
        bold_ranges=None
    ):
        if not text:
            return

        directory = filedialog.askdirectory(
            parent=self.root,
            title='Куда сохранить PNG'
        )

        if not directory:
            return

        directory = Path(
            directory
        )

        default_name = (
            self.get_next_screen_png_name(
                directory
            )
        )

        name = simpledialog.askstring(
            'Сохранить в PNG',
            'Название файла:',
            initialvalue=default_name,
            parent=self.root
        )

        if name is None:
            return

        name = name.strip()

        if not name:
            name = default_name

        if not name.casefold().endswith(
            '.png'
        ):
            name += '.png'

        path = (
            directory / name
        )

        image_width = 1000
        padding = 24

        text_width = (
            image_width
            - padding * 2
        )

        normal_font = (
            self.get_pil_font(
                self.content_font_family,
                max(
                    8,
                    int(
                        self.reader_font_size
                        * 96 / 72
                    )
                ),
                False
            )
        )

        bold_font = (
            self.get_pil_font(
                self.content_font_family,
                max(
                    8,
                    int(
                        self.reader_font_size
                        * 96 / 72
                    )
                ),
                True
            )
        )

        bold_ranges = (
            self.merge_ranges(
                bold_ranges or []
            )
        )

        def is_bold(
            position
        ):
            for a, b in bold_ranges:
                if a <= position < b:
                    return True

                if a > position:
                    break

            return False

        scratch = Image.new(
            'RGB',
            (image_width, 100),
            self.bg_color()
        )

        draw = ImageDraw.Draw(
            scratch
        )

        lines = []

        position = 0
        n = len(text)

        while position < n:
            if text[position] == '\n':
                lines.append(
                    []
                )

                position += 1
                continue

            paragraph_end = text.find(
                '\n',
                position
            )

            if paragraph_end < 0:
                paragraph_end = n

            words = list(
                re.finditer(
                    r'\S+\s*',
                    text[
                        position:
                        paragraph_end
                    ]
                )
            )

            current = []
            current_width = 0

            for match in words:
                start = (
                    position
                    + match.start()
                )

                value = match.group(0)

                font = (
                    bold_font
                    if is_bold(
                        start
                    )
                    else normal_font
                )

                bbox = draw.textbbox(
                    (0, 0),
                    value,
                    font=font
                )

                width = (
                    bbox[2] - bbox[0]
                )

                if (
                    current
                    and current_width
                    + width
                    > text_width
                ):
                    lines.append(
                        current
                    )

                    current = []
                    current_width = 0

                current.append(
                    (
                        value,
                        font
                    )
                )

                current_width += width

            if current:
                lines.append(
                    current
                )

            position = (
                paragraph_end + 1
                if paragraph_end < n
                else n
            )

        line_height = max(
            18,
            int(
                self.reader_font_size
                * 1.75
            )
        )

        gap = 4

        image_height = max(
            padding * 2 + line_height,
            (
                padding * 2
                + len(lines)
                * (
                    line_height + gap
                )
            )
        )

        image = Image.new(
            'RGB',
            (
                image_width,
                image_height
            ),
            self.bg_color()
        )

        draw = ImageDraw.Draw(
            image
        )

        y = padding

        for line_index, line in enumerate(
            lines
        ):
            if not line:
                y += (
                    line_height + gap
                )
                continue

            widths = []

            for value, font in line:
                bbox = draw.textbbox(
                    (0, 0),
                    value,
                    font=font
                )

                widths.append(
                    bbox[2] - bbox[0]
                )

            x = padding

            # Аналог режима full justify.
            if (
                self.content_full_justify
                and line_index
                < len(lines) - 1
                and len(line) > 1
            ):
                base_width = sum(
                    widths
                )

                extra = max(
                    0,
                    text_width - base_width
                ) / float(
                    len(line) - 1
                )
            else:
                extra = 0

            for index, (
                value,
                font
            ) in enumerate(
                line
            ):
                draw.text(
                    (
                        x,
                        y
                    ),
                    value,
                    font=font,
                    fill=self.text_color()
                )

                x += widths[index]

                if index < len(line) - 1:
                    x += extra

            y += (
                line_height + gap
            )

        image.save(
            path,
            'PNG'
        )

    def save_reader_selection_as_png(self):
        ranges = (
            self.get_selected_document_ranges()
        )

        if not ranges:
            return

        pieces = []
        bold = []
        offset = 0

        effective_bold = (
            self.get_reader_effective_bold_ranges()
        )

        for index, (
            start,
            end
        ) in enumerate(
            ranges
        ):
            value = (
                self.reader_content[
                    start:end
                ]
            )

            pieces.append(
                value
            )

            for a, b in effective_bold:
                left = max(
                    a,
                    start
                )

                right = min(
                    b,
                    end
                )

                if right > left:
                    bold.append([
                        offset + left - start,
                        offset + right - start
                    ])

            offset += len(
                value
            )

            if index < len(ranges) - 1:
                pieces.append(
                    '\n'
                )

                offset += 1

        self.save_text_as_png(
            ''.join(
                pieces
            ),
            bold
        )

    def save_notes_selection_as_png(self):
        selection = (
            self.get_notes_selection()
        )

        if not selection:
            return

        start_index, end_index = (
            selection
        )

        start = (
            self.get_note_text_offset(
                start_index
            )
        )

        end = (
            self.get_note_text_offset(
                end_index
            )
        )

        value = self.notes_text.get(
            start_index,
            end_index
        )

        bold = []

        for a, b in self.get_note_tag_ranges(
            'note_bold'
        ):
            left = max(
                a,
                start
            )

            right = min(
                b,
                end
            )

            if right > left:
                bold.append([
                    left - start,
                    right - start
                ])

        self.save_text_as_png(
            value,
            bold
        )

    def on_ctrl_key(
        self,
        event
    ):
        code = getattr(
            event,
            'keycode',
            None
        )

        char = (
            getattr(
                event,
                'char',
                ''
            )
            or ''
        ).lower()

        if code == 67 or char in ('c', 'с'):
            self.copy_text()
            return 'break'

        # Ctrl+W -> Word / CF_HTML.
        if code == 87 or char in ('w', 'ц'):
            self.copy_reader_formatted(
                'html'
            )
            return 'break'

        # Ctrl+M -> Markdown.
        if code == 77 or char in ('m', 'ь'):
            self.copy_reader_formatted(
                'markdown'
            )
            return 'break'

    def show_context_menu(
        self,
        event
    ):
        has_selection = bool(
            self.get_selected_document_ranges()
        )

        # Только Передачи: ПКМ без выделенного текста
        # открывает меню медиа для таймкода под курсором.
        if (
            self.reader_source_type
            == 'transmission'
            and not has_selection
        ):
            return (
                self.show_transmission_media_context_menu(
                    event
                )
            )

        try:
            state = (
                tk.NORMAL
                if has_selection
                else tk.DISABLED
            )

            self.context_menu.entryconfig(
                'Копировать',
                state=state
            )

            self.context_menu.entryconfig(
                'Перенести в заметки',
                state=state
            )

            self.context_menu.entryconfig(
                'Сохранить в PNG',
                state=state
            )

        except Exception:
            pass

        try:
            self.context_menu.tk_popup(
                event.x_root,
                event.y_root
            )

        finally:
            self.context_menu.grab_release()

    def copy_text(self):
        ranges = (
            self.get_selected_document_ranges()
        )

        if not ranges:
            return

        selected = ''.join(
            self.reader_content[
                start:end
            ]
            for start, end
            in ranges
        )

        self.root.clipboard_clear()

        self.root.clipboard_append(
            selected
        )

    # =========================================================
    # FONT
    # =========================================================

    def on_key_press(
        self,
        event
    ):
        if (
            self.current_screen
            != 'reader'
        ):
            return

        if (
            self.search_active
            and self.search_entry
        ):
            try:
                if (
                    self.root.focus_get()
                    is self.search_entry
                ):
                    return

            except Exception:
                pass

        if (
            event.keysym == '2'
            or event.char == '2'
        ):
            self.toggle_reader_two_page_mode()

            return 'break'

        if (
            event.keysym in (
                'plus',
                'equal'
            )
            or event.char in (
                '+',
                '='
            )
        ):
            self.increase_font()

            return 'break'

        if (
            event.keysym in (
                'minus',
                'underscore'
            )
            or event.char in (
                '-',
                '_'
            )
        ):
            self.decrease_font()

            return 'break'

    def increase_font(
        self,
        event=None
    ):
        if not self.text_widget:
            return

        preserve = (
            self.reader_page_start
        )

        self.reader_font_size += 1

        self.apply_reader_font(
            preserve
        )

    def decrease_font(
        self,
        event=None
    ):
        if (
            not self.text_widget
            or self.reader_font_size
            <= 8
        ):
            return

        preserve = (
            self.reader_page_start
        )

        self.reader_font_size -= 1

        self.apply_reader_font(
            preserve
        )

    def apply_reader_font(
        self,
        preserve_position
    ):
        self.reader_font = (
            self.content_font_family,
            self.reader_font_size
        )

        self.reader_font_bold = (
            self.content_font_family,
            self.reader_font_size,
            'bold'
        )

        self.reader_font_italic = (
            self.content_font_family,
            self.reader_font_size,
            'italic'
        )

        self.text_widget.config(
            font=self.reader_font,
            padx=(
                0
                if self.reader_two_page_mode
                else self.text_widget.cget(
                    'padx'
                )
            )
        )

        if (
            self.reader_two_page_mode
            and self.second_text_widget
        ):
            self.second_text_widget.config(
                font=self.reader_font,
                padx=0
            )

        for tag in (
            'speaker',
            'document_bold',
            'title'
        ):
            self.text_widget.tag_config(
                tag,
                font=self.reader_font_bold
            )

        self.root.update_idletasks()

        self.refresh_reader_font_cache()
        self.calculate_reader_lines_per_page()

        self.clear_reader_layout_cache()

        self.reader_back_history = []
        self.reader_forward_history = []

        self.show_reader_page_from_position(
            preserve_position,
            silent_save=True
        )

        self.save_settings()

    # =========================================================
    # SAVE READER POSITION
    # =========================================================

    def schedule_save_position(self):
        if (
            self.suppress_reader_position_save
        ):
            return

        if (
            self.save_timer
            is not None
        ):
            try:
                self.root.after_cancel(
                    self.save_timer
                )

            except Exception:
                pass

        self.save_timer = (
            self.root.after(
                3000,
                self.save_reader_position_now
            )
        )

    def save_reader_position_now(self):
        if (
            self.save_timer
            is not None
        ):
            try:
                self.root.after_cancel(
                    self.save_timer
                )

            except Exception:
                pass

            self.save_timer = None

        if (
            self.suppress_reader_position_save
        ):
            return

        if (
            self.selected_file
            and
            self.current_screen
            == 'reader'
        ):
            self.reading_positions[
                str(
                    self.selected_file
                )
            ] = str(
                self.reader_page_start
            )

            self.save_settings()

    # =========================================================
    # DRAW CURRENT SCREEN / DESTROY
    # =========================================================

    def destroy_reader_widgets(self):
        self.hide_reader_loading()
        if self.search_entry:
            try:
                self.search_entry.destroy()

            except Exception:
                pass

            self.search_entry = None

        if self.second_text_widget:
            try:
                self.second_text_widget.destroy()
            except Exception:
                pass

            self.second_text_widget = None
            self.reader_second_page = None

        if self.text_widget:
            try:
                self.text_widget.destroy()

            except Exception:
                pass

            self.text_widget = None

        if self.reader_container:
            try:
                self.reader_container.destroy()

            except Exception:
                pass

            self.reader_container = None

        self.reader_page_photo_images = []

    def draw_current_screen(
        self,
        start_frame=10
    ):
        self.current_hover = None

        self.scrollbar.pack_forget()

        if (
            self.current_screen
            != 'search'
        ):
            self.destroy_global_search_widgets()

        if (
            self.current_screen
            != 'notes'
        ):
            self.destroy_notes_widgets()

        if (
            self.current_screen
            != 'reader'
        ):
            self.destroy_reader_widgets()

        if (
            self.current_screen
            != 'notes'
            and not self.canvas.winfo_ismapped()
        ):
            self.canvas.pack(
                side=tk.LEFT,
                fill=tk.BOTH,
                expand=True
            )

        self.apply_theme_to_widgets()

        self.root.update_idletasks()

        self.last_size = (
            self.canvas.winfo_width(),
            self.canvas.winfo_height()
        )

        self.canvas.unbind(
            '<MouseWheel>'
        )

        self.canvas.unbind(
            '<Button-4>'
        )

        self.canvas.unbind(
            '<Button-5>'
        )

        self.canvas.unbind(
            '<Button-3>'
        )

        self.root.unbind(
            '<Prior>'
        )

        self.root.unbind(
            '<Next>'
        )

        self.root.unbind(
            '<Key>'
        )

        self.restore_normal_canvas_bindings()

        if (
            self.current_screen
            not in (
                'books',
                'transmissions',
                'files'
            )
        ):
            self.reset_canvas_view()

        if (
            self.current_screen
            == 'home'
        ):
            self.draw_home_screen(
                start_frame
            )

        elif (
            self.current_screen
            == 'search'
        ):
            self.draw_global_search_screen(
                preserve_scroll=True
            )

        elif (
            self.current_screen
            == 'reading'
        ):
            self.draw_reading_screen(
                start_frame
            )

        elif (
            self.current_screen
            == 'books'
        ):
            self.draw_books_screen(
                start_frame
            )

        elif (
            self.current_screen
            == 'transmissions'
        ):
            self.draw_transmissions_screen(
                start_frame
            )

        elif (
            self.current_screen
            == 'projects'
        ):
            self.draw_projects_screen(
                start_frame
            )

        elif (
            self.current_screen
            == 'files'
        ):
            self.draw_files_screen(
                start_frame
            )

        elif (
            self.current_screen
            == 'notes'
        ):
            self.draw_notes_screen()

        elif (
            self.current_screen
            == 'reader'
        ):
            self.draw_reader_screen()

        else:
            self.draw_stub_screen(
                start_frame
            )

        if (
            self.current_screen
            != 'reader'
        ):
            self.current_timecode = (
                '00:00:00'
            )

        self.update_window_title()
        self.build_overlay()

    # =========================================================
    # NORMAL HOVER / CLICK
    # =========================================================

    def on_mousewheel(
        self,
        event
    ):
        if (
            getattr(
                event,
                'num',
                None
            ) == 5
            or
            getattr(
                event,
                'delta',
                0
            ) < 0
        ):
            self.canvas.yview_scroll(
                1,
                'units'
            )

        elif (
            getattr(
                event,
                'num',
                None
            ) == 4
            or
            getattr(
                event,
                'delta',
                0
            ) > 0
        ):
            self.canvas.yview_scroll(
                -1,
                'units'
            )

        return 'break'

    def on_motion(
        self,
        event
    ):
        if (
            self.is_transitioning
            or
            self.current_screen
            in (
                'projects',
                'files',
                'search',
                'notes',
                'reader'
            )
        ):
            return

        x = (
            event.x
        )

        y = (
            self.canvas.canvasy(
                event.y
            )
        )

        hovered = None

        for index, area in enumerate(
            self.hover_areas
        ):
            if (
                area[
                    'left'
                ] <= x
                <= area[
                    'right'
                ]
                and
                area[
                    'top'
                ] <= y
                <= area[
                    'bottom'
                ]
            ):
                hovered = index

                break

        if hovered == self.current_hover:
            return

        if (
            self.current_hover
            is not None
            and self.current_hover
            < len(
                self.highlight_items
            )
        ):
            self.on_item_leave(
                self.current_hover
            )

        self.current_hover = (
            hovered
        )

        if hovered is not None:
            self.on_item_enter(
                hovered
            )

    def on_canvas_leave(
        self,
        event
    ):
        if (
            self.current_screen
            == 'projects'
        ):
            self.set_project_hover(
                None
            )

            return

        if (
            self.current_hover
            is not None
            and not
            self.is_transitioning
        ):
            self.on_item_leave(
                self.current_hover
            )

            self.current_hover = None

    def on_item_enter(
        self,
        index
    ):
        if (
            index >= len(
                self.highlight_items
            )
        ):
            return

        self.highlight_items[
            index
        ][
            'hover_target'
        ] = (
            self.FADE_FRAMES
        )

        self.animate_highlight(
            index
        )

    def on_item_leave(
        self,
        index
    ):
        if (
            index >= len(
                self.highlight_items
            )
        ):
            return

        self.highlight_items[
            index
        ][
            'hover_target'
        ] = 0

        self.animate_highlight(
            index
        )

    def animate_highlight(
        self,
        index
    ):
        if (
            index >= len(
                self.highlight_items
            )
        ):
            return

        item = (
            self.highlight_items[
                index
            ]
        )

        animation_id = (
            item.get(
                'animation_id'
            )
        )

        if animation_id:
            try:
                self.root.after_cancel(
                    animation_id
                )

            except Exception:
                pass

            item[
                'animation_id'
            ] = None

        if (
            item[
                'frame'
            ]
            < item[
                'hover_target'
            ]
        ):
            item[
                'frame'
            ] += 1

        elif (
            item[
                'frame'
            ]
            > item[
                'hover_target'
            ]
        ):
            item[
                'frame'
            ] -= 1

        try:
            self.canvas.itemconfig(
                item[
                    'item'
                ],
                image=(
                    item[
                        'frames'
                    ][
                        item[
                            'frame'
                        ]
                    ]
                    if item.get(
                        'type'
                    ) == 'home_scaled'
                    else
                    self.photo_frames[
                        item[
                            'key'
                        ]
                    ][
                        item[
                            'frame'
                        ]
                    ]
                )
            )

        except Exception:
            return

        if (
            item[
                'frame'
            ]
            != item[
                'hover_target'
            ]
        ):
            item[
                'animation_id'
            ] = (
                self.root.after(
                    self.FADE_DELAY,
                    lambda:
                    self.animate_highlight(
                        index
                    )
                )
            )

    def on_click(
        self,
        event
    ):
        if (
            self.current_screen
            == 'files'
        ):
            return (
                self.on_files_click(
                    event
                )
            )

        if (
            self.is_transitioning
            or
            self.current_screen
            in (
                'projects',
                'search',
                'notes',
                'reader'
            )
        ):
            return

        if self.current_hover is None:
            return

        index = (
            self.current_hover
        )

        if (
            index >= len(
                self.highlight_items
            )
        ):
            return

        if (
            self.current_screen
            == 'transmissions'
        ):
            self.remember_transmissions_view()

        elif (
            self.current_screen
            == 'books'
        ):
            self.remember_books_view()

        self.is_transitioning = (
            True
        )

        item = (
            self.highlight_items[
                index
            ]
        )

        self.canvas.coords(
            item[
                'item'
            ],
            item[
                'x'
            ],
            item[
                'y'
            ]
            + self.CLICK_OFFSET
        )

        self.root.after(
            self.CLICK_DELAY,
            lambda:
            self.click_release(
                index
            )
        )

    def click_release(
        self,
        index
    ):
        if (
            index < len(
                self.highlight_items
            )
        ):
            item = (
                self.highlight_items[
                    index
                ]
            )

            try:
                self.canvas.coords(
                    item[
                        'item'
                    ],
                    item[
                        'x'
                    ],
                    item[
                        'y'
                    ]
                )

            except Exception:
                pass

        target = (
            self.get_target_screen(
                index
            )
        )

        self.fade_out_screen(
            lambda:
            self.change_screen(
                target
            )
        )

    def get_target_screen(
        self,
        index
    ):
        if (
            self.current_screen
            == 'home'
        ):
            targets = (
                'search',
                'reading',
                'notes'
            )

            if index < len(
                targets
            ):
                return (
                    targets[
                        index
                    ]
                )

            return 'home'

        if (
            self.current_screen
            == 'reading'
        ):
            targets = (
                'books',
                'transmissions',
                'projects',
                'files'
            )

            if index >= len(
                targets
            ):
                return 'reading'

            target = (
                targets[
                    index
                ]
            )

            if target == 'books':
                self.books_yview = 0.0
                self.restore_books_view = False

            elif (
                target
                == 'transmissions'
            ):
                self.transmissions_yview = 0.0
                self.restore_transmissions_view = False

            elif (
                target
                == 'files'
            ):
                self.files_yview = 0.0
                self.restore_files_view = False

            return target

        if (
            self.current_screen
            == 'books'
            and
            index < len(
                self.books_list
            )
        ):
            self.reader_from_global_search = False
            self.suppress_reader_position_save = False

            self.selected_file = (
                self.books_list[
                    index
                ][
                    'filepath'
                ]
            )

            self.selected_source_type = (
                'book'
            )

            return 'reader'

        if (
            self.current_screen
            == 'transmissions'
            and
            index < len(
                self.transmissions_list
            )
        ):
            self.reader_from_global_search = False
            self.suppress_reader_position_save = False

            self.selected_file = (
                self.transmissions_list[
                    index
                ][
                    'filepath'
                ]
            )

            self.selected_source_type = (
                'transmission'
            )

            return 'reader'

        return 'home'

    # =========================================================
    # FADE
    # =========================================================

    def fade_out_screen(
        self,
        callback
    ):
        for item in (
            self.highlight_items
        ):
            animation = (
                item.get(
                    'animation_id'
                )
            )

            if animation:
                try:
                    self.root.after_cancel(
                        animation
                    )

                except Exception:
                    pass

                item[
                    'animation_id'
                ] = None

        for element in (
            self.screen_elements
        ):
            element[
                'fade_target'
            ] = 0

        self.animate_fade(
            callback
        )

    def animate_fade(
        self,
        callback=None
    ):
        done = True

        for element in (
            self.screen_elements
        ):
            if (
                element[
                    'frame'
                ]
                < element[
                    'fade_target'
                ]
            ):
                element[
                    'frame'
                ] += 1

                done = False

            elif (
                element[
                    'frame'
                ]
                > element[
                    'fade_target'
                ]
            ):
                element[
                    'frame'
                ] -= 1

                done = False

            try:
                if (
                    element[
                        'type'
                    ] == 'image'
                ):
                    self.canvas.itemconfig(
                        element[
                            'item'
                        ],
                        image=self.photo_frames[
                            element[
                                'key'
                            ]
                        ][
                            element[
                                'frame'
                            ]
                        ]
                    )

                elif (
                    element[
                        'type'
                    ] == 'home_scaled'
                ):
                    self.canvas.itemconfig(
                        element[
                            'item'
                        ],
                        image=element[
                            'frames'
                        ][
                            element[
                                'frame'
                            ]
                        ]
                    )

                else:
                    colors = (
                        self.text_fade_colors_semi
                        if element.get(
                            'semi'
                        )
                        else
                        self.text_fade_colors
                    )

                    self.canvas.itemconfig(
                        element[
                            'item'
                        ],
                        fill=colors[
                            element[
                                'frame'
                            ]
                        ]
                    )

            except Exception:
                pass

        if not done:
            self.root.after(
                self.FADE_DELAY,
                lambda:
                self.animate_fade(
                    callback
                )
            )

        elif callback:
            callback()

    # =========================================================
    # CHANGE SCREEN
    # =========================================================

    def change_screen(
        self,
        screen
    ):
        old_screen = (
            self.current_screen
        )

        if (
            old_screen == 'search'
            and screen != 'search'
        ):
            self.cancel_global_search_debounce()

        if (
            old_screen
            == 'notes'
        ):
            self.cancel_notes_save_timer()

            self.save_current_note_sheet(
                save_settings_now=True
            )

        if (
            old_screen
            == 'search'
            and
            self.global_search_canvas
        ):
            try:
                view = (
                    self.global_search_canvas.yview()
                )

                if view:
                    self.global_search_saved_yview = (
                        float(
                            view[0]
                        )
                    )

            except Exception:
                pass

        self.current_screen = (
            screen
        )

        self.update_window_title()

        if (
            screen
            == 'reader'
        ):
            self.draw_current_screen()

            self.is_transitioning = False

            return

        if (
            screen
            not in (
                'notes',
            )
            and
            not self.canvas.winfo_ismapped()
        ):
            self.canvas.pack(
                side=tk.LEFT,
                fill=tk.BOTH,
                expand=True
            )

            self.root.update_idletasks()

        if (
            screen
            not in (
                'books',
                'transmissions',
                'files'
            )
        ):
            self.reset_canvas_view()

        if screen in (
            'projects',
            'files',
            'search',
            'notes'
        ):
            self.is_transitioning = False

            self.draw_current_screen(
                10
            )

            self.is_transitioning = False

            return

        self.draw_current_screen(
            0
        )

        for element in (
            self.screen_elements
        ):
            element[
                'fade_target'
            ] = (
                0
                if element.get(
                    'is_highlight'
                )
                else
                self.FADE_FRAMES
            )

        self.animate_fade(
            self.finish_transition
        )

    def finish_transition(self):
        self.is_transitioning = (
            False
        )

    # =========================================================
    # HOME / BACK / ESC
    # =========================================================

    def go_home(self):
        if (
            self.current_screen
            == 'home'
        ):
            return

        if (
            self.current_screen
            == 'notes'
        ):
            self.save_current_note_sheet(
                save_settings_now=True
            )

        if (
            self.current_screen
            == 'reader'
            and not
            self.suppress_reader_position_save
        ):
            self.save_reader_position_now()

        self.reader_from_global_search = False
        self.suppress_reader_position_save = False

        self.global_search_target_position = (
            None
        )

        self.is_transitioning = False

        self.change_screen(
            'home'
        )

    def go_back(self):
        self.on_escape(
            None
        )

    def on_escape(
        self,
        event=None
    ):
        # Reader from global search returns directly
        # to that exact global-search state.
        if (
            self.current_screen
            == 'reader'
            and
            self.reader_from_global_search
        ):
            self.restore_global_search_after_reader()

            return 'break'

        if (
            self.current_screen
            == 'reader'
            and
            self.search_active
        ):
            self.close_search()

            return 'break'

        if (
            self.current_screen
            == 'home'
        ):
            return

        if (
            self.current_screen
            == 'notes'
            and self.notes_search_active
        ):
            self.close_notes_search()

            return 'break'

        if (
            self.current_screen
            == 'notes'
        ):
            self.save_current_note_sheet(
                save_settings_now=True
            )

            target = (
                'home'
            )

        elif (
            self.current_screen
            == 'reader'
        ):
            self.save_reader_position_now()

            if (
                self.reader_source_type
                == 'book'
            ):
                self.restore_books_view = True
                target = 'books'

            elif (
                self.reader_source_type
                == 'project'
            ):
                target = 'projects'

            elif (
                self.reader_source_type
                == 'external'
            ):
                self.restore_files_view = True
                target = 'files'

            else:
                self.restore_transmissions_view = True
                target = 'transmissions'

        elif (
            self.current_screen
            in (
                'books',
                'transmissions',
                'projects',
                'files'
            )
        ):
            target = (
                'reading'
            )

        elif (
            self.current_screen
            in (
                'reading',
                'search'
            )
        ):
            target = (
                'home'
            )

        else:
            target = (
                'home'
            )

        self.is_transitioning = False

        self.change_screen(
            target
        )

        return 'break'

    # =========================================================
    # STUB
    # =========================================================

    def draw_stub_screen(
        self,
        start_frame=10
    ):
        self.reset_canvas_view()

        self.canvas.delete(
            'all'
        )

        self.canvas.configure(
            bg=self.bg_color()
        )

        width = max(
            1,
            self.canvas.winfo_width()
        )

        height = max(
            1,
            self.canvas.winfo_height()
        )

        self.canvas.config(
            scrollregion=(
                0,
                0,
                width,
                height
            )
        )

        self.screen_elements = []
        self.highlight_items = []
        self.hover_areas = []

    # =========================================================
    # RESIZE
    # =========================================================

    def on_configure(
        self,
        event
    ):
        if event.widget != self.root:
            return

        try:
            if self.root.state() == 'normal':
                self.window_geometry = (
                    f'{self.root.winfo_width()}'
                    'x'
                    f'{self.root.winfo_height()}'
                )

                self.window_position = (
                    f'+{self.root.winfo_x()}'
                    f'+{self.root.winfo_y()}'
                )
        except Exception:
            pass

        size = (
            self.root.winfo_width(),
            self.root.winfo_height()
        )

        previous = getattr(
            self,
            '_last_root_size',
            None
        )

        # Windows может присылать Configure при
        # потере/возврате фокуса. Если размер не
        # изменился, ничего не перерисовываем.
        if previous == size:
            return

        self._last_root_size = size

        if self.resize_timer:
            try:
                self.root.after_cancel(
                    self.resize_timer
                )
            except Exception:
                pass

        self.resize_timer = self.root.after(
            250,
            self.on_resize_redraw
        )

    def on_resize_redraw(self):
        self.resize_timer = None

        if (
            self.current_screen
            == 'reader'
            and
            self.text_widget
        ):
            preserve = (
                self.reader_page_start
            )

            if (
                self.reader_two_page_mode
                and self.second_text_widget
            ):
                self.layout_two_page_reader()

                self.root.update_idletasks()

            if (
                self.search_active
                and
                self.search_entry
            ):
                try:
                    self.search_query = (
                        self.search_entry.get()
                    )

                except Exception:
                    pass

            width = (
                self.reader_container
                .winfo_width()
            )

            padding = (
                0
                if self.reader_two_page_mode
                else
                self.get_reader_side_padding(
                    width
                )
            )

            self.text_widget.config(
                padx=padding
            )

            if (
                self.reader_two_page_mode
                and self.second_text_widget
            ):
                self.second_text_widget.config(
                    padx=0
                )

            self.root.update_idletasks()

            self.refresh_reader_font_cache()
            self.calculate_reader_lines_per_page()

            self.clear_reader_layout_cache()

            self.reader_back_history = []
            self.reader_forward_history = []

            self.show_reader_page_from_position(
                preserve,
                silent_save=True
            )

            return

        if (
            self.current_screen
            == 'search'
        ):
            if self.global_search_entry:
                try:
                    self.global_search_query = (
                        self.global_search_entry.get()
                    )

                except Exception:
                    pass

            if self.global_search_canvas:
                try:
                    view = (
                        self.global_search_canvas.yview()
                    )

                    if view:
                        self.global_search_saved_yview = (
                            float(
                                view[0]
                            )
                        )

                except Exception:
                    pass

            self.draw_global_search_screen(
                preserve_scroll=True
            )

            self.build_overlay()

            return

        if (
            self.current_screen
            == 'notes'
        ):
            self.save_current_note_sheet()

            if (
                self.notes_search_active
                and self.notes_search_entry
            ):
                try:
                    self.notes_search_query = (
                        self.notes_search_entry.get()
                    )
                except Exception:
                    pass

            # build_overlay использует ровно тот же
            # determine_search_layout(), что reader:
            # wide / narrow / hiding side icons.
            self.apply_notes_width_mode()

            self.build_overlay()

            # Ещё одна отрисовка только нижней панели
            # после окончательного resize Tk.
            if self.notes_tabs_layout_timer is not None:
                try:
                    self.root.after_cancel(
                        self.notes_tabs_layout_timer
                    )
                except Exception:
                    pass

            self.notes_tabs_layout_timer = (
                self.root.after(
                    40,
                    self.draw_notes_bottom_bar
                )
            )

            return

        if (
            self.current_screen
            == 'books'
        ):
            self.remember_books_view()

            self.restore_books_view = True

            self.draw_current_screen(
                10
            )

            return

        if (
            self.current_screen
            == 'transmissions'
        ):
            self.remember_transmissions_view()

            self.restore_transmissions_view = True

            self.draw_current_screen(
                10
            )

            return

        if (
            self.current_screen
            == 'files'
        ):
            self.remember_files_view()

            self.restore_files_view = True

            self.draw_current_screen(
                10
            )

            return

        if (
            self.current_screen
            == 'projects'
        ):
            self.draw_projects_screen(
                10
            )

            self.build_overlay()

            return

        self.draw_current_screen(
            10
        )

    # =========================================================
    # CLOSE
    # =========================================================

    def on_closing(self):
        if self.help_window:
            self.close_help_window()

        if self.settings_window:
            # Application shutdown keeps current preview
            # exactly like OK.
            self.settings_preview_active = False

            try:
                self.settings_window.destroy()
            except Exception:
                pass

            self.settings_window = None

        self.cancel_global_search_debounce()

        if (
            self.current_screen
            == 'notes'
        ):
            self.cancel_notes_save_timer()

            self.save_current_note_sheet()

        if (
            self.current_screen
            == 'reader'
            and not
            self.suppress_reader_position_save
        ):
            self.save_reader_position_now()

        self.save_settings()

        self.root.destroy()

    def run(self):
        self.root.mainloop()


if __name__ == '__main__':
    app = RaReader()
    app.run()