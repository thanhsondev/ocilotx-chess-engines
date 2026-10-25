# Prompt gửi Claude

Bạn là kỹ sư chess engine Lua/Luau. Hãy đọc và nâng cấp mã thực tế trong repo `thanhsondev/ocilotx-chess-engines` để cải thiện chất lượng nước đi trong ngân sách mặc định 2.5 giây trên Roblox.

Đọc trước:
- `engines/Nova.lua`, `engines/Lith.lua`, `engines/Null.lua`, `engines/Muse.lua`.
- `README.md`, `SOURCES.json` và `tests/engine_smoke.lua`.

Nếu không truy cập được repo hoặc chưa có đủ file, nói rõ file nào thiếu; không tự nhận đã đọc. Tôi có thể đính kèm mã.

## 1. Phân tích hiện trạng

Lập bảng từng engine: thuật toán tìm kiếm, đánh giá thế cờ, quản lý thời gian, phong cách hiện có, điểm yếu tìm thấy. Dẫn tên hàm hoặc đoạn mã làm bằng chứng. Phân biệt tính năng đã có với tính năng bạn đề xuất bổ sung.

Ưu tiên nâng cấp `Nova.lua`, tên hiển thị **OcilotX Nova**. Có thể cải thiện các engine khác nếu có lợi ích đo được. Giữ nguồn tác giả và thông tin xuất xứ.

## 2. Tương thích bắt buộc

- Mỗi file vẫn trả về bảng engine; giữ cách gọi `engine:GetBestMoveFromFEN(fen, seconds)` và kết quả `move, score[, reaction]`.
- Nước đi dùng UCI: `e2e4`, `a7a8q`. Kiểm tra đầy đủ tính hợp lệ; không để vua mình bị chiếu. Không có nước hợp lệ thì trả nil, không bịa nước đi.
- Giữ quy ước điểm số và các phương thức/đối số tùy chọn đang được sử dụng: `SetStyle`, `Analyze`, `Perft`, `GetPV`, `MakeMoveFEN`, history/options nếu file có chúng.
- Không thêm HTTP, API key, provider AI, tải mã từ xa, thao tác GUI, đọc tài khoản hay gửi nước đi vào game. Engine chỉ tính cờ.
- Không sửa AutoPlay, phím tắt hoặc dashboard. Host luôn tắt AutoPlay khi load; mặc định engine Nova và thời gian 2.5 giây.
- Không dựa vào việc Lua có số nguyên 64-bit chính xác. Kiểm tra các thao tác bit và hash trong môi trường Luau thực tế.

## 3. Các hướng nâng cấp cần đánh giá

Xem xét cải thiện iterative deepening, alpha-beta/PVS, transposition table, sắp xếp nước đi, quiescence search, SEE và pruning. Chỉ bổ sung khi phù hợp với mã hiện có; tránh triển khai lại thứ đã hoạt động tốt.

Tăng khả năng xử lý các tình huống:
- Đòn đôi, ghim, xiên, chiếu mở, bắt quân không được bảo vệ và phòng ngừa mất quân.
- Tấn công vua, an toàn vua và các chuỗi chiếu/bắt quân/nước đe dọa.
- Hoạt động quân, trung tâm, cột mở, ô yếu, cấu trúc tốt.
- Tốt thông, hoạt động vua và chuyển đổi ưu thế trong tàn cuộc.
- Nhập thành, bắt tốt qua đường, phong cấp và underpromotion.
- Chiếu hết, pat, hòa do thiếu lực lượng, luật 50 nước và lặp lại nếu có lịch sử phù hợp. Một FEN đơn lẻ không đủ để suy ra toàn bộ lịch sử lặp lại.

Các phong cách hiện có là Balanced, Aggressive, Calm, Defensive, Tactical, Trickery, Positional, Endgame, Alien Gambit, Willy Alien. Đề xuất phong cách mới có hành vi cụ thể, tham số rõ ràng và cách kiểm chứng. Phong cách không được biến một nước sai luật thành hợp lệ hoặc bỏ qua chiếu hết bắt buộc. Nếu thêm tên phong cách, ghi rõ thay đổi tích hợp host/dashboard cần làm; chưa có mã host thì không tự sửa cấu trúc đó.

## 4. Ngân sách thời gian

Kiểm tra deadline đều trong search và quiescence; có cooperative yielding để không làm treo Roblox. Khi hết giờ, giữ nước hợp lệ từ vòng tìm kiếm hoàn tất gần nhất; có fallback hợp lệ nếu chưa hoàn tất depth đầu. Không ghi kết quả tìm kiếm dở dang vào TT như exact score. Xem xét các trường trạng thái ảnh hưởng luật cờ khi dùng lại cache.

Đo trước/sau ở 0.5s, 1s và 2.5s trên cùng tập vị trí và cùng môi trường. Báo thời gian thực, mức vượt ngân sách, depth hoàn tất, nodes nếu có và số bài chiến thuật giải được. Không cam kết thời gian tuyệt đối nếu scheduler không bảo đảm.

## 5. Kiểm chứng và bàn giao

Chạy smoke/perft hiện có; bổ sung regression cho lỗi bạn thực sự sửa. Dùng các vị trí có đáp án độc lập hoặc engine tham chiếu để kiểm tra chiến thuật. Đừng lấy chính thuật toán mới làm nguồn chân lý cho bài kiểm tra của nó.

Nếu chạy self-play để so sánh, dùng cùng ngân sách, đổi bên trên cùng khai cuộc và báo số ván/thắng/hòa/thua. Không tự suy ra Elo hoặc tỷ lệ thắng tuyệt đối từ ít ván.

Trả về:
1. Các vấn đề có bằng chứng và phương án sửa được chọn.
2. File Lua hoàn chỉnh hoặc patch áp dụng được, không dùng dấu ba chấm thay mã.
3. Test và lệnh chạy; kết quả thực tế, nêu rõ phần chưa chạy được.
4. Bảng benchmark trước/sau và giới hạn của phép đo.
5. Danh sách phong cách mới, mô tả, tên cấu hình và yêu cầu tích hợp.

Làm các thay đổi nhỏ có thể kiểm tra riêng, giữ những phần chưa cần sửa và tiếp tục đến khi có mã chạy được.
