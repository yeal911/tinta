// Direct2D + DirectWrite renderer for Windows
// Much faster startup than OpenGL

#include "app.h"

#include <windowsx.h>
#include <shellapi.h>
#include <commdlg.h>
#include <shlobj.h>

#include <fstream>
#include <sstream>
#include <algorithm>
#include <cstdio>
#include <functional>
#include "settings.h"
#include "d2d_init.h"
#include "utils.h"
#include "syntax.h"
#include "search.h"
#include "render.h"
#include "file_utils.h"
#include "overlays.h"
#include "input.h"
#include "editor.h"

static App* g_app = nullptr;

// Forward declarations
LRESULT CALLBACK WndProc(HWND hwnd, UINT msg, WPARAM wParam, LPARAM lParam);
void render(App& app);

void render(App& app) {
    if (!app.renderTarget) return;

    app.renderTarget->BeginDraw();
    app.drawCalls = 0;

    if (app.layoutDirty) {
        layoutDocument(app);
    }

    // Edit mode scroll synchronization between editor and preview panes.
    if (app.editMode && !app.scrollAnchors.empty() && !app.editorLineByteOffsets.empty()) {
        float lineHeight = app.editorTextFormat ? app.editorTextFormat->GetFontSize() * 1.5f : 20.0f;
        float padding = dpi(app, 8.0f);

        if (app.editScrollSyncSource == App::EditScrollSyncSource::Editor) {
            float topContentY = app.editorScrollY + padding;
            float topLineF = std::max(0.0f, topContentY / std::max(1.0f, lineHeight));
            int topLine = std::max(0, std::min((int)topLineF, (int)app.editorLineByteOffsets.size() - 1));
            int nextLine = std::min(topLine + 1, (int)app.editorLineByteOffsets.size() - 1);
            float frac = std::max(0.0f, std::min(1.0f, topLineF - topLine));
            size_t topByteOffset = app.editorLineByteOffsets[topLine] +
                (size_t)((app.editorLineByteOffsets[nextLine] - app.editorLineByteOffsets[topLine]) * frac);

            size_t lo = 0, hi = app.scrollAnchors.size();
            while (lo + 1 < hi) {
                size_t mid = (lo + hi) / 2;
                if (app.scrollAnchors[mid].sourceOffset <= topByteOffset) lo = mid;
                else hi = mid;
            }

            float targetY;
            if (lo + 1 < app.scrollAnchors.size() &&
                app.scrollAnchors[lo + 1].sourceOffset > app.scrollAnchors[lo].sourceOffset) {
                float t = (float)(topByteOffset - app.scrollAnchors[lo].sourceOffset) /
                          (float)(app.scrollAnchors[lo + 1].sourceOffset - app.scrollAnchors[lo].sourceOffset);
                t = std::max(0.0f, std::min(t, 1.0f));
                targetY = app.scrollAnchors[lo].renderedY +
                           t * (app.scrollAnchors[lo + 1].renderedY - app.scrollAnchors[lo].renderedY);
            } else {
                targetY = app.scrollAnchors[lo].renderedY;
                if (app.contentHeight > app.scrollAnchors[lo].renderedY) {
                    size_t lastOffset = app.scrollAnchors[lo].sourceOffset;
                    size_t totalBytes = app.editorLineByteOffsets.back();
                    if (totalBytes > lastOffset) {
                        float t = (float)(topByteOffset - lastOffset) / (float)(totalBytes - lastOffset);
                        t = std::max(0.0f, std::min(t, 1.0f));
                        targetY += t * (app.contentHeight - app.scrollAnchors[lo].renderedY);
                    }
                }
            }

            float previewMaxScroll = std::max(0.0f, app.contentHeight - contentViewportHeight(app));
            app.scrollY = std::max(0.0f, std::min(targetY, previewMaxScroll));
            app.targetScrollY = app.scrollY;
        } else {
            // Preview drives sync: map preview Y back to editor byte offset and then line position.
            float previewY = app.scrollY;

            size_t lo = 0, hi = app.scrollAnchors.size();
            while (lo + 1 < hi) {
                size_t mid = (lo + hi) / 2;
                if (app.scrollAnchors[mid].renderedY <= previewY) lo = mid;
                else hi = mid;
            }

            size_t topByteOffset = app.scrollAnchors[lo].sourceOffset;
            if (lo + 1 < app.scrollAnchors.size() &&
                app.scrollAnchors[lo + 1].renderedY > app.scrollAnchors[lo].renderedY) {
                float t = (previewY - app.scrollAnchors[lo].renderedY) /
                          (app.scrollAnchors[lo + 1].renderedY - app.scrollAnchors[lo].renderedY);
                t = std::max(0.0f, std::min(t, 1.0f));
                topByteOffset = app.scrollAnchors[lo].sourceOffset +
                    (size_t)((app.scrollAnchors[lo + 1].sourceOffset - app.scrollAnchors[lo].sourceOffset) * t);
            }

            auto it = std::upper_bound(app.editorLineByteOffsets.begin(), app.editorLineByteOffsets.end(), topByteOffset);
            size_t lineIdx = (it == app.editorLineByteOffsets.begin()) ? 0 : (size_t)(it - app.editorLineByteOffsets.begin() - 1);
            size_t nextIdx = std::min(lineIdx + 1, app.editorLineByteOffsets.size() - 1);

            float lineFrac = 0.0f;
            size_t lineStartByte = app.editorLineByteOffsets[lineIdx];
            size_t nextStartByte = app.editorLineByteOffsets[nextIdx];
            if (nextStartByte > lineStartByte) {
                lineFrac = (float)(topByteOffset - lineStartByte) / (float)(nextStartByte - lineStartByte);
                lineFrac = std::max(0.0f, std::min(lineFrac, 1.0f));
            }

            float targetEditorY = (lineIdx + lineFrac) * lineHeight - padding;
            float editorMaxScroll = std::max(0.0f, app.editorContentHeight - (float)app.height);
            app.editorScrollY = std::max(0.0f, std::min(targetEditorY, editorMaxScroll));
        }
    }

    // Edit mode: split view rendering
    if (app.editMode) {
        app.renderTarget->Clear(app.theme.background);

        float editorWidth = app.width * app.editorSplitRatio - 3;
        float previewX = app.width * app.editorSplitRatio + 3;
        float previewWidth = app.width - previewX;

        // Render editor (left pane)
        renderEditor(app, editorWidth);

        // Render separator
        renderSeparator(app);

        // Render preview (right pane) using clip + transform
        app.renderTarget->PushAxisAlignedClip(
            D2D1::RectF(previewX, 0, (float)app.width, (float)app.height),
            D2D1_ANTIALIAS_MODE_ALIASED);

        D2D1_MATRIX_3X2_F originalTransform;
        app.renderTarget->GetTransform(&originalTransform);
        app.renderTarget->SetTransform(
            D2D1::Matrix3x2F::Translation(previewX, 0) * originalTransform);

        // Clear preview background
        app.brush->SetColor(app.theme.background);
        app.renderTarget->FillRectangle(
            D2D1::RectF(0, 0, previewWidth, (float)app.height), app.brush);

        goto render_document;
    }

    // Clear background
    app.renderTarget->Clear(app.theme.background);
    app.drawCalls++;

render_document:

    const float viewportHeight = contentViewportHeight(app);
    app.renderTarget->PushAxisAlignedClip(
        D2D1::RectF(0, 0, (float)app.width, viewportHeight),
        D2D1_ANTIALIAS_MODE_PER_PRIMITIVE);

    // Clamp scroll values
    float maxScrollX = std::max(0.0f, app.contentWidth - app.width);
    float maxScrollY = std::max(0.0f, app.contentHeight - contentViewportHeight(app));
    app.scrollX = std::max(0.0f, std::min(app.scrollX, maxScrollX));
    app.scrollY = std::max(0.0f, std::min(app.scrollY, maxScrollY));

    // Render cached layout (document coordinates -> screen)
    const float viewportTop = app.scrollY;
    const float viewportBottom = app.scrollY + contentViewportHeight(app);
    const float viewportLeft = app.scrollX;
    const float viewportRight = app.scrollX + app.width;
    const float cullMargin = 100.0f;

    for (const auto& rect : app.layoutRects) {
        if (rect.rect.bottom < viewportTop - cullMargin ||
            rect.rect.top > viewportBottom + cullMargin) {
            continue;
        }
        if (rect.rect.right < viewportLeft - cullMargin ||
            rect.rect.left > viewportRight + cullMargin) {
            continue;
        }
        app.brush->SetColor(rect.color);
        app.renderTarget->FillRectangle(
            D2D1::RectF(rect.rect.left - app.scrollX, rect.rect.top - app.scrollY,
                       rect.rect.right - app.scrollX, rect.rect.bottom - app.scrollY),
            app.brush);
        app.drawCalls++;
    }

    // Render images (bitmaps)
    for (const auto& bmp : app.layoutBitmaps) {
        if (!bmp.bitmap) continue;
        if (bmp.destRect.bottom < viewportTop - cullMargin ||
            bmp.destRect.top > viewportBottom + cullMargin) continue;
        if (bmp.destRect.right < viewportLeft - cullMargin ||
            bmp.destRect.left > viewportRight + cullMargin) continue;
        app.renderTarget->DrawBitmap(bmp.bitmap,
            D2D1::RectF(bmp.destRect.left - app.scrollX,
                         bmp.destRect.top - app.scrollY,
                         bmp.destRect.right - app.scrollX,
                         bmp.destRect.bottom - app.scrollY));
        app.drawCalls++;
    }

    for (const auto& run : app.layoutTextRuns) {
        if (run.bounds.bottom < viewportTop - cullMargin ||
            run.bounds.top > viewportBottom + cullMargin) {
            continue;
        }
        if (run.bounds.right < viewportLeft - cullMargin ||
            run.bounds.left > viewportRight + cullMargin) {
            continue;
        }
        app.brush->SetColor(run.color);
        D2D1_POINT_2F drawPos = D2D1::Point2F(run.pos.x - app.scrollX, run.pos.y - app.scrollY);
        if (app.deviceContext) {
            app.deviceContext->DrawTextLayout(drawPos, run.layout, app.brush,
                D2D1_DRAW_TEXT_OPTIONS_ENABLE_COLOR_FONT);
        } else {
            app.renderTarget->DrawTextLayout(drawPos, run.layout, app.brush);
        }
        app.drawCalls++;
    }

    for (const auto& line : app.layoutLines) {
        float minY = std::min(line.p1.y, line.p2.y);
        float maxY = std::max(line.p1.y, line.p2.y);
        if (maxY < viewportTop - cullMargin || minY > viewportBottom + cullMargin) {
            continue;
        }
        app.brush->SetColor(line.color);
        app.renderTarget->DrawLine(
            D2D1::Point2F(line.p1.x - app.scrollX, line.p1.y - app.scrollY),
            D2D1::Point2F(line.p2.x - app.scrollX, line.p2.y - app.scrollY),
            app.brush, line.stroke);
        app.drawCalls++;
    }

    // Render code block copy button on hover
    if (app.hoveredCodeBlock >= 0 && app.hoveredCodeBlock < (int)app.codeBlocks.size()) {
        const auto& cb = app.codeBlocks[app.hoveredCodeBlock];
        if (cb.bounds.bottom >= viewportTop - cullMargin &&
            cb.bounds.top <= viewportBottom + cullMargin) {
            float btnW = dpi(app, 52.0f);
            float btnH = dpi(app, 26.0f);
            float btnPad = 8.0f * app.contentScale * app.zoomFactor;
            float btnX = cb.bounds.right - btnW - btnPad - app.scrollX;
            float btnY = cb.bounds.top + btnPad - app.scrollY;

            // Button background
            app.brush->SetColor(D2D1::ColorF(
                app.theme.isDark ? 0.3f : 0.85f,
                app.theme.isDark ? 0.3f : 0.85f,
                app.theme.isDark ? 0.3f : 0.85f,
                0.9f));
            app.renderTarget->FillRoundedRectangle(
                D2D1::RoundedRect(D2D1::RectF(btnX, btnY, btnX + btnW, btnY + btnH), 4, 4),
                app.brush);

            // "Copy" label centered in button
            app.brush->SetColor(D2D1::ColorF(
                app.theme.isDark ? 0.9f : 0.15f,
                app.theme.isDark ? 0.9f : 0.15f,
                app.theme.isDark ? 0.9f : 0.15f,
                1.0f));
            IDWriteTextLayout* btnLayout = nullptr;
            app.dwriteFactory->CreateTextLayout(L"Copy", 4, app.codeFormat,
                btnW, btnH, &btnLayout);
            if (btnLayout) {
                btnLayout->SetTextAlignment(DWRITE_TEXT_ALIGNMENT_CENTER);
                btnLayout->SetParagraphAlignment(DWRITE_PARAGRAPH_ALIGNMENT_CENTER);
                app.renderTarget->DrawTextLayout(
                    D2D1::Point2F(btnX, btnY), btnLayout, app.brush);
                btnLayout->Release();
            }
            app.drawCalls++;
        }
    }

    // Determine scrollbar visibility
    bool needsVScroll = app.contentHeight > contentViewportHeight(app);
    bool needsHScroll = app.contentWidth > app.width;
    float scrollbarSize = dpi(app, 14.0f);

    // Scrollbar color: dark on light themes, light on dark themes
    float sbColorValue = app.theme.isDark ? 1.0f : 0.0f;

    // Draw vertical scrollbar
    if (needsVScroll) {
        float maxScrollY = std::max(0.0f, app.contentHeight - contentViewportHeight(app));
        float trackHeight = contentViewportHeight(app) - (needsHScroll ? scrollbarSize : 0);
        float sbHeight = trackHeight / app.contentHeight * trackHeight;
        sbHeight = std::max(sbHeight, dpi(app, 30.0f));
        float sbY = (maxScrollY > 0) ? (app.scrollY / maxScrollY * (trackHeight - sbHeight)) : 0;

        float sbWidth = (app.scrollbarHovered || app.scrollbarDragging) ? dpi(app, 10.0f) : dpi(app, 6.0f);
        float sbAlpha = (app.scrollbarHovered || app.scrollbarDragging) ? 0.5f : 0.3f;

        app.brush->SetColor(D2D1::ColorF(sbColorValue, sbColorValue, sbColorValue, sbAlpha));
        app.renderTarget->FillRoundedRectangle(
            D2D1::RoundedRect(D2D1::RectF(app.width - sbWidth - dpi(app, 4.0f), sbY,
                                          app.width - dpi(app, 4.0f), sbY + sbHeight), 3, 3),
            app.brush);
        app.drawCalls++;
    }

    // Draw horizontal scrollbar
    if (needsHScroll) {
        float maxScrollX = std::max(0.0f, app.contentWidth - app.width);
        float trackWidth = app.width - (needsVScroll ? scrollbarSize : 0);
        float sbWidth = trackWidth / app.contentWidth * trackWidth;
        sbWidth = std::max(sbWidth, dpi(app, 30.0f));
        float sbX = (maxScrollX > 0) ? (app.scrollX / maxScrollX * (trackWidth - sbWidth)) : 0;

        float sbHeight = (app.hScrollbarHovered || app.hScrollbarDragging) ? dpi(app, 10.0f) : dpi(app, 6.0f);
        float sbAlpha = (app.hScrollbarHovered || app.hScrollbarDragging) ? 0.5f : 0.3f;

        app.brush->SetColor(D2D1::ColorF(sbColorValue, sbColorValue, sbColorValue, sbAlpha));
        app.renderTarget->FillRoundedRectangle(
            D2D1::RoundedRect(D2D1::RectF(sbX, contentViewportHeight(app) - sbHeight - dpi(app, 4.0f),
                                          sbX + sbWidth, contentViewportHeight(app) - dpi(app, 4.0f)), 3, 3),
            app.brush);
        app.drawCalls++;
    }

    // Draw selection highlights
    if ((app.selecting || app.hasSelection) && !app.textRects.empty()) {
        // Calculate selection bounds (normalized so start is always before end)
        // Selection is stored in document coordinates
        float selStartX = (float)app.selStartX;
        float selStartY = (float)app.selStartY;
        float selEndX = (float)app.selEndX;
        float selEndY = (float)app.selEndY;

        // Swap if selection was made bottom-to-top
        if (selStartY > selEndY || (selStartY == selEndY && selStartX > selEndX)) {
            std::swap(selStartX, selEndX);
            std::swap(selStartY, selEndY);
        }

        // Check if this is a "select all" (selectedText is set but selection coords are same)
        bool isSelectAll = app.hasSelection && !app.selectedText.empty() &&
                          app.selStartX == app.selEndX && app.selStartY == app.selEndY;

        app.brush->SetColor(D2D1::ColorF(0.2f, 0.4f, 0.9f, 0.35f));

        const auto& lines = app.lineBuckets;

        std::wstring collectedText;
        size_t selectedCount = 0;

        for (size_t i = 0; i < lines.size(); i++) {
            const auto& line = lines[i];
            float lineCenterY = (line.top + line.bottom) / 2;

            bool lineInSelection = false;
            float drawLeft = line.minX;
            float drawRight = line.maxX;

            if (isSelectAll) {
                lineInSelection = true;
            } else if (lineCenterY >= selStartY - 3 && lineCenterY <= selEndY + 3) {
                float lineHeight = line.bottom - line.top;
                bool isSingleLine = (selEndY - selStartY) <= lineHeight;

                if (isSingleLine) {
                    // Single line selection
                    drawLeft = std::max(line.minX, selStartX);
                    drawRight = std::min(line.maxX, selEndX);
                    if (drawLeft < drawRight) lineInSelection = true;
                } else if (lineCenterY < selStartY + lineHeight) {
                    // First line - from selection start to end of line
                    drawLeft = std::max(line.minX, selStartX);
                    lineInSelection = true;
                } else if (lineCenterY > selEndY - lineHeight) {
                    // Last line - from start of line to selection end
                    drawRight = std::min(line.maxX, selEndX);
                    lineInSelection = true;
                } else {
                    // Middle line - full width
                    lineInSelection = true;
                }
            }

            if (lineInSelection) {
                // Draw continuous selection bar for this line
                app.renderTarget->FillRectangle(
                    D2D1::RectF(drawLeft - app.scrollX, line.top - app.scrollY,
                                drawRight - app.scrollX, line.bottom - app.scrollY),
                    app.brush);
                selectedCount++;

                // Collect text from rects in this line that fall within selection
                if (!collectedText.empty()) collectedText += L"\n";
                for (size_t idx : line.textRectIndices) {
                    const auto& tr = app.textRects[idx];
                    const D2D1_RECT_F& rect = tr.rect;
                    if (rect.left < drawRight && rect.right > drawLeft) {
                        if (!collectedText.empty() && collectedText.back() != L'\n') {
                            collectedText += L" ";
                        }
                        std::wstring_view slice = textViewForRect(app, tr);
                        collectedText.append(slice.data(), slice.size());
                    }
                }
            }
        }
        app.drawCalls += selectedCount;

        // Update selectedText for mouse selections (not select-all)
        if (!isSelectAll && app.hasSelection && selectedCount > 0) {
            app.selectedText = collectedText;
        }
    }

    // Draw search match highlights (search live through visible textRects)
    if (app.showSearch && !app.searchQuery.empty() && !app.textRects.empty() && !app.searchMatches.empty()) {
        // Collect visible match rects by intersecting search matches with text rects
        struct VisibleMatch {
            D2D1_RECT_F rect;
            size_t matchIndex;
        };
        std::vector<VisibleMatch> visibleMatches;

        size_t matchIndex = 0;
        for (const auto& tr : app.textRects) {
            size_t textLen = tr.docLength;
            if (textLen == 0) continue;

            size_t rectStart = tr.docStart;
            size_t rectEnd = rectStart + textLen;

            // Advance to first match that could overlap this rect
            while (matchIndex < app.searchMatches.size()) {
                const auto& m = app.searchMatches[matchIndex];
                size_t mEnd = m.startPos + m.length;
                if (mEnd <= rectStart) {
                    matchIndex++;
                    continue;
                }
                break;
            }

            size_t mi = matchIndex;
            while (mi < app.searchMatches.size()) {
                const auto& m = app.searchMatches[mi];
                if (m.startPos >= rectEnd) break;

                size_t mStart = m.startPos;
                size_t mEnd = m.startPos + m.length;
                size_t overlapStart = std::max(rectStart, mStart);
                size_t overlapEnd = std::min(rectEnd, mEnd);

                if (overlapStart < overlapEnd) {
                    float totalWidth = tr.rect.right - tr.rect.left;
                    float charWidth = totalWidth / (float)textLen;
                    float startX = tr.rect.left + (overlapStart - rectStart) * charWidth;
                    float matchWidth = (overlapEnd - overlapStart) * charWidth;

                    // Extend highlight slightly for better visibility
                    D2D1_RECT_F highlightRect = D2D1::RectF(
                        startX - 1, tr.rect.top,
                        startX + matchWidth + 1, tr.rect.bottom
                    );

                    visibleMatches.push_back({highlightRect, mi});
                }

                if (mEnd <= rectEnd) {
                    mi++;
                } else {
                    break;  // Match spans beyond this rect; continue on next rect
                }
            }

            matchIndex = mi;
        }

        // Draw all matches - orange if it's the current match, yellow otherwise
        for (const auto& vm : visibleMatches) {
            bool isCurrent = (app.searchCurrentIndex >= 0 &&
                              vm.matchIndex == (size_t)app.searchCurrentIndex);

            if (isCurrent) {
                app.brush->SetColor(D2D1::ColorF(1.0f, 0.6f, 0.0f, 0.5f));  // Orange
            } else {
                app.brush->SetColor(D2D1::ColorF(1.0f, 0.9f, 0.0f, 0.3f));  // Yellow
            }

            app.renderTarget->FillRectangle(
                D2D1::RectF(vm.rect.left - app.scrollX, vm.rect.top - app.scrollY,
                            vm.rect.right - app.scrollX, vm.rect.bottom - app.scrollY),
                app.brush);
            app.drawCalls++;
        }
    }

    // "Copied!" notification with fade out (cached layout)
    if (app.showCopiedNotification) {
        auto now = std::chrono::steady_clock::now();
        float elapsed = std::chrono::duration<float>(now - app.copiedNotificationStart).count();

        if (elapsed < 2.0f) {
            float alpha = 1.0f;
            if (elapsed > 0.5f) {
                alpha = 1.0f - (elapsed - 0.5f) / 1.5f;
            }
            app.copiedNotificationAlpha = alpha;

            float copyWidth = dpi(app, 100.0f);
            float copyHeight = dpi(app, 26.0f);
            float pillX = (app.width - copyWidth) / 2;
            float pillY = dpi(app, 10.0f);

            app.brush->SetColor(D2D1::ColorF(0.2f, 0.7f, 0.3f, 0.9f * alpha));
            app.renderTarget->FillRoundedRectangle(
                D2D1::RoundedRect(D2D1::RectF(pillX, pillY, pillX + copyWidth, pillY + copyHeight), 13, 13),
                app.brush);

            // Cache the "Copied!" text layout and metrics across frames
            static IDWriteTextLayout* cachedCopyLayout = nullptr;
            static float cachedTextOffsetX = 0, cachedTextOffsetY = 0;
            if (!cachedCopyLayout) {
                app.dwriteFactory->CreateTextLayout(L"Copied!", 7,
                    app.textFormat, copyWidth, copyHeight, &cachedCopyLayout);
                if (cachedCopyLayout) {
                    DWRITE_TEXT_METRICS m;
                    cachedCopyLayout->GetMetrics(&m);
                    cachedTextOffsetX = (copyWidth - m.width) / 2;
                    cachedTextOffsetY = (copyHeight - m.height) / 2;
                }
            }
            if (cachedCopyLayout) {
                app.brush->SetColor(D2D1::ColorF(1, 1, 1, alpha));
                app.renderTarget->DrawTextLayout(
                    D2D1::Point2F(pillX + cachedTextOffsetX, pillY + cachedTextOffsetY),
                    cachedCopyLayout, app.brush);
            }
            app.drawCalls++;
            InvalidateRect(app.hwnd, nullptr, FALSE);
        } else {
            app.showCopiedNotification = false;
        }
    }

    // Draw stats
    if (app.showStats) {
        wchar_t stats[512];
        swprintf(stats, 512,
            L"Parse: %zu us | Draw calls: %zu\n"
            L"Startup: %.1fms (Win: %.1f | D2D: %.1f | DWrite: %.1f | File: %.1f)",
            app.parseTimeUs,
            app.drawCalls,
            app.metrics.totalStartupUs / 1000.0,
            app.metrics.windowInitUs / 1000.0,
            app.metrics.d2dInitUs / 1000.0,
            app.metrics.dwriteInitUs / 1000.0,
            app.metrics.fileLoadUs / 1000.0);

        float statsWidth = dpi(app, 600.0f);
        float statsHeight = dpi(app, 50.0f);

        app.brush->SetColor(D2D1::ColorF(0, 0, 0, 0.8f));
        app.renderTarget->FillRectangle(
            D2D1::RectF(app.width - statsWidth - dpi(app, 10.0f), app.height - statsHeight - dpi(app, 10.0f),
                       app.width - dpi(app, 10.0f), app.height - dpi(app, 10.0f)),
            app.brush);

        app.brush->SetColor(D2D1::ColorF(0.7f, 0.9f, 0.7f));
        app.renderTarget->DrawText(stats, (UINT32)wcslen(stats), app.codeFormat,
            D2D1::RectF(app.width - statsWidth - dpi(app, 5.0f), app.height - statsHeight - dpi(app, 5.0f),
                       app.width - dpi(app, 15.0f), app.height - dpi(app, 15.0f)),
            app.brush);
    }

    // Render overlays (search overlay handled separately for edit mode)
    if (app.showSearch && !app.editMode) renderSearchOverlay(app);
    if (app.showFolderBrowser) renderFolderBrowser(app);
    if (app.showToc) renderToc(app);
    if (app.showHelpPanel && !app.editMode) renderHelpPanel(app);
    if (app.showThemeChooser) renderThemeChooser(app);

    // Close edit mode split view clipping
    if (app.editMode) {
        D2D1_MATRIX_3X2_F identity = D2D1::Matrix3x2F::Identity();
        app.renderTarget->SetTransform(identity);
        app.renderTarget->PopAxisAlignedClip();

        // Render search overlay in screen coordinates (over editor pane)
        if (app.showSearch) renderSearchOverlay(app);

        // Render edit mode notification (on top of everything)
        renderEditModeNotification(app);

        // Render help panel in screen coordinates over preview pane (same layer as TOC)
        if (app.showHelpPanel) renderHelpPanel(app);
    }

    app.renderTarget->PopAxisAlignedClip();

    // Bottom status bar with key shortcuts (always visible)
    {
        const wchar_t* shortcuts =
            L"B - Folder | Tab - TOC | F/Ctrl+F - Search | T - Theme | : - Edit | Ctrl+S - Save | F1 - Help | Esc - Close/Quit";
        float barHeight = statusBarHeight(app);
        float padX = dpi(app, 10.0f);

        D2D1_COLOR_F barColor = app.theme.isDark ? hexColor(0x0F1115) : hexColor(0xFFE4E4);
        barColor.a = 1.0f;
        app.brush->SetColor(barColor);
        app.renderTarget->FillRectangle(
            D2D1::RectF(0, app.height - barHeight, (float)app.width, (float)app.height),
            app.brush);

        D2D1_COLOR_F textColor = app.theme.isDark ? D2D1::ColorF(1, 1, 1, 1) : D2D1::ColorF(0.2f, 0.2f, 0.2f, 1);
        app.brush->SetColor(textColor);
        IDWriteTextFormat* statusFmt = app.statusBarFormat ? app.statusBarFormat : app.searchTextFormat;
        if (statusFmt) {
            float rightW = dpi(app, 280.0f);
            app.renderTarget->DrawText(
                shortcuts,
                (UINT32)wcslen(shortcuts),
                statusFmt,
                D2D1::RectF(padX, app.height - barHeight, app.width - rightW, (float)app.height),
                app.brush);

            size_t totalChars = app.editMode ? app.editorText.size() : app.docText.size();
            std::wstring rightInfo = L"Chars - " + std::to_wstring(totalChars);
            if (app.editMode && !app.editorLineStarts.empty()) {
                auto it = std::upper_bound(app.editorLineStarts.begin(), app.editorLineStarts.end(), app.editorCursorPos);
                size_t lineIdx = (it == app.editorLineStarts.begin()) ? 0 : (size_t)(it - app.editorLineStarts.begin() - 1);
                size_t col = app.editorCursorPos - app.editorLineStarts[lineIdx];
                rightInfo += L"   Ln - " + std::to_wstring(lineIdx + 1) + L", Col - " + std::to_wstring(col + 1);
            }

            statusFmt->SetTextAlignment(DWRITE_TEXT_ALIGNMENT_TRAILING);
            app.renderTarget->DrawText(
                rightInfo.c_str(),
                (UINT32)rightInfo.length(),
                statusFmt,
                D2D1::RectF(app.width - rightW, app.height - barHeight, app.width - padX, (float)app.height),
                app.brush);
            statusFmt->SetTextAlignment(DWRITE_TEXT_ALIGNMENT_LEADING);
        }
    }

    // "Saved!" notification (reuses "Copied!" infrastructure)

    app.renderTarget->EndDraw();
}

LRESULT CALLBACK WndProc(HWND hwnd, UINT msg, WPARAM wParam, LPARAM lParam) {
    App* app = g_app;

    switch (msg) {
        case WM_SIZE:
            if (app && app->d2dFactory) {
                app->width = LOWORD(lParam);
                app->height = HIWORD(lParam);
                createRenderTarget(*app);
                app->layoutDirty = true;
                InvalidateRect(hwnd, nullptr, FALSE);
            }
            return 0;

        case WM_DPICHANGED:
            if (app) {
                UINT dpi = HIWORD(wParam);
                app->contentScale = dpi / 96.0f;

                // Resize window to suggested new size
                RECT* newRect = (RECT*)lParam;
                SetWindowPos(hwnd, nullptr,
                    newRect->left, newRect->top,
                    newRect->right - newRect->left,
                    newRect->bottom - newRect->top,
                    SWP_NOZORDER | SWP_NOACTIVATE);

                // Recreate text formats and render target for new DPI
                updateTextFormats(*app);
                createRenderTarget(*app);
                InvalidateRect(hwnd, nullptr, FALSE);
            }
            return 0;

        case WM_PAINT: {
            PAINTSTRUCT ps;
            BeginPaint(hwnd, &ps);
            if (app) render(*app);
            EndPaint(hwnd, &ps);
            return 0;
        }

        case WM_MOUSEWHEEL:
            if (app) handleMouseWheel(*app, hwnd, wParam, lParam);
            return 0;

        case WM_MOUSEHWHEEL:
            if (app) handleMouseHWheel(*app, hwnd, wParam, lParam);
            return 0;

        case WM_MOUSEMOVE:
            if (app) handleMouseMove(*app, hwnd, lParam);
            return 0;

        case WM_LBUTTONDOWN:
            if (app) handleMouseDown(*app, hwnd, wParam, lParam);
            return 0;

        case WM_LBUTTONUP:
            if (app) handleMouseUp(*app, hwnd, wParam, lParam);
            return 0;

        case WM_SETCURSOR:
            if (app && LOWORD(lParam) == HTCLIENT) {
                // We handle cursor in WM_MOUSEMOVE
                return TRUE;
            }
            break;

        case WM_KEYDOWN:
            if (app) handleKeyDown(*app, hwnd, wParam);
            return 0;

        case WM_CHAR:
            if (app) handleCharInput(*app, hwnd, wParam);
            return 0;

        case WM_DROPFILES:
            if (app) handleDropFiles(*app, hwnd, wParam);
            return 0;

        case WM_TIMER:
            if (wParam == TIMER_FILE_WATCH && app) handleFileWatchTimer(*app, hwnd);
            if (wParam == 2 && app) editorReparse(*app); // TIMER_EDITOR_REPARSE
            return 0;

        case WM_DESTROY:
            KillTimer(hwnd, TIMER_FILE_WATCH);
            KillTimer(hwnd, 2); // TIMER_EDITOR_REPARSE
            {
                // Load existing settings to preserve values like hasAskedFileAssociation
                Settings settings = loadSettings();
                settings.themeIndex = app->currentThemeIndex;
                settings.zoomFactor = app->zoomFactor;
                settings.fontSize = app->configuredFontSize;
                if (!app->configuredFontFamily.empty()) {
                    int len = WideCharToMultiByte(CP_UTF8, 0, app->configuredFontFamily.c_str(), -1, nullptr, 0, nullptr, nullptr);
                    if (len > 1) {
                        settings.fontFamily.resize(len - 1);
                        WideCharToMultiByte(CP_UTF8, 0, app->configuredFontFamily.c_str(), -1, &settings.fontFamily[0], len, nullptr, nullptr);
                    }
                }

                // Get window placement for position/size/maximized state
                WINDOWPLACEMENT wp = {};
                wp.length = sizeof(wp);
                if (GetWindowPlacement(hwnd, &wp)) {
                    settings.windowMaximized = (wp.showCmd == SW_SHOWMAXIMIZED);
                    // Save the restored (non-maximized) position
                    settings.windowX = wp.rcNormalPosition.left;
                    settings.windowY = wp.rcNormalPosition.top;
                    settings.windowWidth = wp.rcNormalPosition.right - wp.rcNormalPosition.left;
                    settings.windowHeight = wp.rcNormalPosition.bottom - wp.rcNormalPosition.top;
                }

                saveSettings(settings);
            }
            PostQuitMessage(0);
            return 0;
    }

    return DefWindowProcW(hwnd, msg, wParam, lParam);
}

static const char* sampleMarkdown = R"(# Welcome to Tinta

**Tinta** is a fast, lightweight markdown reader for Windows.

## Features

- Lightning-fast startup with Direct2D
- Hardware-accelerated text rendering via DirectWrite
- Minimal dependencies
- Small binary size

## Code Example

```cpp
int main() {
    printf("Hello, World!\n");
    return 0;
}
```

## Keyboard Shortcuts

- **F** or **Ctrl+F** - Open search
- **T** - Open theme chooser
- **S** - Toggle stats overlay
- **Ctrl+C** - Copy text
- **Ctrl+A** - Select all
- **Q** or **ESC** - Quit
)";

int WINAPI WinMain(HINSTANCE hInstance, HINSTANCE, LPSTR lpCmdLine, int nCmdShow) {
    // Enable per-monitor DPI V2 awareness
    SetProcessDpiAwarenessContext(DPI_AWARENESS_CONTEXT_PER_MONITOR_AWARE_V2);

    auto startupStart = Clock::now();

    App app;
    auto t0 = startupStart;
    g_app = &app;

    // Load saved settings
    Settings savedSettings = loadSettings();
    app.currentThemeIndex = savedSettings.themeIndex;
    app.theme = THEMES[savedSettings.themeIndex];
    app.darkMode = app.theme.isDark;
    app.zoomFactor = savedSettings.zoomFactor;
    app.configuredFontFamily = toWide(savedSettings.fontFamily);
    if (app.configuredFontFamily.empty()) app.configuredFontFamily = L"Microsoft YaHei UI";
    app.configuredFontSize = savedSettings.fontSize;

    // Parse command line
    std::string inputFile;
    bool lightMode = false;
    bool forceRegister = false;

    int argc;
    LPWSTR* argv = CommandLineToArgvW(GetCommandLineW(), &argc);
    for (int i = 1; i < argc; i++) {
        std::wstring arg = argv[i];
        if (arg == L"-l" || arg == L"--light") {
            lightMode = true;
        } else if (arg == L"-s" || arg == L"--stats") {
            app.showStats = true;
        } else if (arg == L"/register" || arg == L"--register") {
            forceRegister = true;
        } else if (arg[0] != L'-' && arg[0] != L'/') {
            // Convert to UTF-8
            int len = WideCharToMultiByte(CP_UTF8, 0, arg.c_str(), -1, nullptr, 0, nullptr, nullptr);
            inputFile.resize(len - 1);
            WideCharToMultiByte(CP_UTF8, 0, arg.c_str(), -1, &inputFile[0], len, nullptr, nullptr);
        }
    }
    LocalFree(argv);

    // Handle /register command
    if (forceRegister) {
        if (registerFileAssociation()) {
            MessageBoxW(nullptr,
                       L"Tinta has been registered.\n\n"
                       L"In the Settings window that opens:\n"
                       L"1. Search for '.md'\n"
                       L"2. Click on the current default app\n"
                       L"3. Select 'Tinta' from the list",
                       L"Almost done!", MB_OK | MB_ICONINFORMATION);
            openDefaultAppsSettings();
        } else {
            MessageBoxW(nullptr, L"Failed to register file association. Try running as administrator.",
                       L"Error", MB_OK | MB_ICONWARNING);
        }
        return 0;  // Exit after registering
    }

    // Ask about file association on first run
    askAndRegisterFileAssociation(savedSettings);

    // One-time quick-start hint for discoverability
    if (!savedSettings.hasShownQuickStartHint) {
        MessageBoxW(nullptr,
            L"Quick start:\n"
            L"- F1: keyboard shortcuts\n"
            L"- : enter edit mode\n"
            L"- Ctrl+F: search\n"
            L"- B / Tab: folder browser / table of contents\n"
            L"- T: theme chooser",
            L"Tinta - Quick Start",
            MB_OK | MB_ICONINFORMATION);
        savedSettings.hasShownQuickStartHint = true;
        saveSettings(savedSettings);
    }

    if (lightMode) {
        app.currentThemeIndex = 0;  // Paper (first light theme)
        app.theme = THEMES[0];
        app.darkMode = false;
    }

    // Create window with saved position/size
    t0 = Clock::now();

    WNDCLASSEXW wc = {};
    wc.cbSize = sizeof(wc);
    wc.style = CS_HREDRAW | CS_VREDRAW;
    wc.lpfnWndProc = WndProc;
    wc.hInstance = hInstance;
    wc.hCursor = LoadCursor(nullptr, IDC_ARROW);
    wc.hIcon = LoadIconW(hInstance, L"IDI_ICON1");
    wc.hIconSm = LoadIconW(hInstance, L"IDI_ICON1");
    wc.lpszClassName = L"Tinta";
    RegisterClassExW(&wc);

    app.hwnd = CreateWindowExW(
        WS_EX_ACCEPTFILES,
        L"Tinta",
        L"Tinta",
        WS_OVERLAPPEDWINDOW,
        savedSettings.windowX, savedSettings.windowY,
        savedSettings.windowWidth, savedSettings.windowHeight,
        nullptr, nullptr, hInstance, nullptr
    );

    app.metrics.windowInitUs = usElapsed(t0);

    // Get DPI using per-monitor aware API
    app.contentScale = GetDpiForWindow(app.hwnd) / 96.0f;

    // Initialize D2D
    if (!initD2D(app)) {
        MessageBoxW(nullptr, L"Failed to initialize Direct2D", L"Error", MB_OK);
        return 1;
    }

    // Create text formats and typography
    updateTextFormats(app);
    createTypography(app);

    // Get window size
    RECT rc;
    GetClientRect(app.hwnd, &rc);
    app.width = rc.right - rc.left;
    app.height = rc.bottom - rc.top;

    // Create render target
    t0 = Clock::now();
    if (!createRenderTarget(app)) {
        MessageBoxW(nullptr, L"Failed to create render target", L"Error", MB_OK);
        return 1;
    }
    app.metrics.renderTargetUs = usElapsed(t0);

    // Load document
    t0 = Clock::now();

    auto loadMarkdown = [&](const std::string& content) {
        auto result = app.parser.parse(content);
        if (result.success) {
            app.root = result.root;
            app.parseTimeUs = result.parseTimeUs;
        }
    };

    auto loadFile = [&](const std::string& path) -> bool {
        // Use wide string path for ifstream to support non-ASCII paths (MSVC extension)
        std::wstring widePath = toWide(path);
        std::ifstream file(widePath);
        if (!file) return false;
        std::stringstream buffer;
        buffer << file.rdbuf();
        loadMarkdown(buffer.str());
        return true;
    };

    if (!inputFile.empty()) {
        loadFile(inputFile);
        app.currentFile = inputFile;
    } else {
        // Try syntax.md
        if (loadFile("syntax.md")) {
            app.currentFile = "syntax.md";
        } else {
            loadMarkdown(sampleMarkdown);
        }
    }

    app.metrics.fileLoadUs = usElapsed(t0);

    // Set window title with filename
    updateWindowTitle(app);

    // Start file watch timer and record initial write time
    updateFileWriteTime(app);
    SetTimer(app.hwnd, TIMER_FILE_WATCH, 500, nullptr);

    // Show window (respect saved maximized state)
    t0 = Clock::now();
    if (savedSettings.windowMaximized) {
        ShowWindow(app.hwnd, SW_SHOWMAXIMIZED);
    } else {
        ShowWindow(app.hwnd, nCmdShow);
    }
    UpdateWindow(app.hwnd);
    app.metrics.showWindowUs = usElapsed(t0);

    app.metrics.totalStartupUs = usElapsed(startupStart);

    // Message loop
    MSG msg;
    while (GetMessage(&msg, nullptr, 0, 0)) {
        TranslateMessage(&msg);
        DispatchMessage(&msg);
    }

    g_app = nullptr;
    return (int)msg.wParam;
}
