#include "storage/index/b_plus_tree.h"

#include <sstream>
#include <string>

#include "buffer/lru_k_replacer.h"
#include "common/config.h"
#include "common/exception.h"
#include "common/logger.h"
#include "common/macros.h"
#include "common/rid.h"
#include "storage/index/index_iterator.h"
#include "storage/page/b_plus_tree_header_page.h"
#include "storage/page/b_plus_tree_internal_page.h"
#include "storage/page/b_plus_tree_leaf_page.h"
#include "storage/page/b_plus_tree_page.h"
#include "storage/page/page_guard.h"

namespace bustub {

    INDEX_TEMPLATE_ARGUMENTS
    BPLUSTREE_TYPE::BPlusTree(std::string name, page_id_t header_page_id,
                              BufferPoolManager* buffer_pool_manager,
                              const KeyComparator& comparator, int leaf_max_size,
                              int internal_max_size)
        : index_name_(std::move(name)),
          bpm_(buffer_pool_manager),
          comparator_(std::move(comparator)),
          leaf_max_size_(leaf_max_size),
          internal_max_size_(internal_max_size),
          header_page_id_(header_page_id) {
        WritePageGuard guard = bpm_->FetchPageWrite(header_page_id_);
        // In the original bpt, I fetch the header page
        // thus there's at least one page now
        auto root_header_page = guard.template AsMut<BPlusTreeHeaderPage>();
        // reinterprete the data of the page into "HeaderPage"
        root_header_page->root_page_id_ = INVALID_PAGE_ID;
        // set the root_id to INVALID
    }

    /*
     * Helper function to decide whether current b+tree is empty
     */
    INDEX_TEMPLATE_ARGUMENTS
    auto BPLUSTREE_TYPE::IsEmpty() const -> bool {
        ReadPageGuard guard = bpm_->FetchPageRead(header_page_id_);
        auto root_header_page = guard.template As<BPlusTreeHeaderPage>();
        bool is_empty = root_header_page->root_page_id_ == INVALID_PAGE_ID;
        // Just check if the root_page_id is INVALID
        // usage to fetch a page:
        // fetch the page guard   ->   call the "As" function of the page guard
        // to reinterprete the data of the page as "BPlusTreePage"
        return is_empty;
    }
    /*****************************************************************************
     * SEARCH
     *****************************************************************************/
    /*
     * Return the only value that associated with input key
     * This method is used for point query
     * @return : true means key exists
     */
    INDEX_TEMPLATE_ARGUMENTS
    auto BPLUSTREE_TYPE::GetValue(const KeyType& key,
                                  std::vector<ValueType>* result, Transaction* txn)
        -> bool {

        if (header_page_id_ == INVALID_PAGE_ID) return false;
        ReadPageGuard guard = bpm_->FetchPageRead(header_page_id_);
        page_id_t x = guard.template As<BPlusTreeHeaderPage>()->root_page_id_;
        guard = bpm_->FetchPageRead(x);
        auto x_page = guard.template As<BPlusTreePage>();
        const InternalPage *internal_page;
        const LeafPage *leaf_page;
        while (!x_page->IsLeafPage()) {
            internal_page = guard.template As<InternalPage>();
            x = internal_page->ValueAt(BinaryFind(internal_page, key));
            guard = bpm_->FetchPageRead(x);
            x_page = guard.template As<BPlusTreePage>();
        }

        leaf_page = guard.template As<LeafPage>();
        int pos = BinaryFind(leaf_page, key);
        if (pos<0 || comparator_(leaf_page->KeyAt(pos), key)!=0) return false;
        result->push_back(leaf_page->ValueAt(pos));
        return true;
    }

    /*****************************************************************************
     * INSERTION
     *****************************************************************************/
    /*
     * Insert constant key & value pair into b+ tree
     * if current tree is empty, start new tree, update root page id and insert
     * entry, otherwise insert into leaf page.
     * @return: since we only support unique key, if user try to insert duplicate
     * keys return false, otherwise return true.
     */

    INDEX_TEMPLATE_ARGUMENTS
    auto BPLUSTREE_TYPE::Insert(const KeyType& key, const ValueType& value,
                                Transaction* txn) -> bool {
        Context ctx;
        ctx.header_page_ = bpm_->FetchPageWrite(header_page_id_);
        auto header_page = ctx.header_page_.value().template AsMut<BPlusTreeHeaderPage>();
        if (header_page->root_page_id_ == INVALID_PAGE_ID) {
            // start new tree
            page_id_t new_root_page_id;
            auto new_root_guard = bpm_->NewPageGuarded(&new_root_page_id).UpgradeWrite();
            auto new_root_page = new_root_guard.template AsMut<LeafPage>();
            new_root_page->Init();
            new_root_page->SetSize(1);
            new_root_page->SetKeyAt(0, key);
            new_root_page->SetValueAt(0, value);
            new_root_page->SetNextPageId(INVALID_PAGE_ID);
            header_page->root_page_id_ = new_root_page_id;
            return true;
        }
        ctx.root_page_id_ = header_page->root_page_id_;
        ctx.header_page_ = std::nullopt;

        page_id_t x = ctx.root_page_id_;
        while (true) {
            ctx.write_set_.emplace_back(bpm_->FetchPageWrite(x));
            if (ctx.write_set_.back().template As<BPlusTreePage>()->IsLeafPage()) {
                break;
            }
            auto x_page = ctx.write_set_.back().template As<InternalPage>();
            if (x_page->GetSize() < x_page->GetMaxSize()-1) {
                for (; ctx.write_set_.size() > 1; ctx.write_set_.pop_front());
            }
            x = x_page->ValueAt(BinaryFind(x_page, key));
        }

        auto leaf_page = ctx.write_set_.back().template AsMut<LeafPage>();
        if (!InsertAt(leaf_page, key, value)) { // If key has already existed
            return false;
        }

        while (ctx.write_set_.size()>1) {
            page_id_t rpage_id;
            KeyType mid_key;
            if (ctx.write_set_.back().template As<BPlusTreePage>()->IsLeafPage()) {
                auto page = ctx.write_set_.back().template AsMut<LeafPage>();
                mid_key = SplitPage(page, rpage_id);
            } else {
                auto page = ctx.write_set_.back().template AsMut<InternalPage>();
                mid_key = SplitPage(page, rpage_id);
            }
            ctx.write_set_.pop_back();
            auto x_page = ctx.write_set_.back().template AsMut<InternalPage>();
            InsertAt(x_page, mid_key, rpage_id);
        }

        auto temp_page = ctx.write_set_.back().template As<BPlusTreePage>();
        if (temp_page->GetSize() == temp_page->GetMaxSize()) {
            page_id_t new_root_id, rpage_id;
            KeyType mid_key;
            auto new_root_guard = bpm_->NewPageGuarded(&new_root_id).UpgradeWrite();
            auto new_root_page = new_root_guard.template AsMut<InternalPage>();
            new_root_page->SetSize(2);
            new_root_page->SetValueAt(0, ctx.write_set_.back().PageId());
            if (temp_page->IsLeafPage()) {
                auto page = ctx.write_set_.back().template AsMut<LeafPage>();
                mid_key = SplitPage(page, rpage_id);
            } else {
                auto page = ctx.write_set_.back().template AsMut<InternalPage>();
                mid_key = SplitPage(page, rpage_id);
            }
            new_root_page->SetKeyAt(1, mid_key);
            new_root_page->SetValueAt(1, rpage_id);

            ctx.header_page_ = bpm_->FetchPageWrite(header_page_id_);
            ctx.header_page_.value().template AsMut<BPlusTreeHeaderPage>()->root_page_id_ = new_root_id;
            ctx.header_page_ = std::nullopt;
        }

        return true;
    }

    /*****************************************************************************
     * REMOVE
     *****************************************************************************/
    /*
     * Delete key & value pair associated with input key
     * If current tree is empty, return immediately.
     * If not, User needs to first find the right leaf page as deletion target, then
     * delete entry from leaf page. Remember to deal with redistribute or merge if
     * necessary.
     */

    INDEX_TEMPLATE_ARGUMENTS
    void BPLUSTREE_TYPE::Remove(const KeyType& key, Transaction* txn) {
        // Your code here
    }

    /*****************************************************************************
     * Helper functions
    ******************************************************************************/

    /*
    * Move from pos to the right by one node
    */
    INDEX_TEMPLATE_ARGUMENTS
    void BPLUSTREE_TYPE::MoveRight(InternalPage* page, int pos) {
        page->IncreaseSize(1);
        for (int i = page->GetSize() - 1; i > pos; i--) {
            page->SetKeyAt(i, page->KeyAt(i - 1));
            page->SetValueAt(i, page->ValueAt(i - 1));
        }
    }

    INDEX_TEMPLATE_ARGUMENTS
    void BPLUSTREE_TYPE::MoveRight(LeafPage* page, int pos) {
        page->IncreaseSize(1);
        for (int i = page->GetSize() - 1; i > pos; i--) {
            page->SetKeyAt(i, page->KeyAt(i - 1));
            page->SetValueAt(i, page->ValueAt(i - 1));
        }
    }

    /*
    * Split a page
    */
    INDEX_TEMPLATE_ARGUMENTS
    KeyType BPLUSTREE_TYPE::SplitPage(InternalPage* lpage, page_id_t& new_page_id) {
        WritePageGuard new_page_guard = bpm_->NewPageGuarded(&new_page_id).UpgradeWrite();
        InternalPage* rpage = new_page_guard.template AsMut<InternalPage>();
        rpage->Init();
        int lsize = lpage->GetSize()/2, rsize = lpage->GetSize() - lsize;
        rpage->SetSize(rsize);
        KeyType mid_key = lpage->KeyAt(lsize);
        for (int i = lsize; i<lpage->GetSize(); i++) {
            if (i > lsize) {
                rpage->SetKeyAt(i - lsize, lpage->KeyAt(i));
            }
            rpage->SetValueAt(i - lsize, lpage->ValueAt(i));
        }
        lpage->SetSize(lsize);
        return mid_key;
    }

    INDEX_TEMPLATE_ARGUMENTS
    KeyType BPLUSTREE_TYPE::SplitPage(LeafPage* lpage, page_id_t& new_page_id) {
        WritePageGuard new_page_guard = bpm_->NewPageGuarded(&new_page_id).UpgradeWrite();
        LeafPage* rpage = new_page_guard.template AsMut<LeafPage>();
        rpage->Init();
        rpage->SetNextPageId(lpage->GetNextPageId());
        lpage->SetNextPageId(new_page_id);
        int lsize = lpage->GetSize()/2, rsize = lpage->GetSize() - lsize;
        KeyType mid_key = lpage->KeyAt(lsize);
        rpage->SetSize(rsize);
        for (int i = lsize; i<lpage->GetSize(); i++) {
            if (i > lsize) {
                rpage->SetKeyAt(i - lsize, lpage->KeyAt(i));
            }
            rpage->SetValueAt(i - lsize, lpage->ValueAt(i));
        }
        lpage->SetSize(lsize);
        return mid_key;
    }

    /*
    * Merge two pages
    */
    INDEX_TEMPLATE_ARGUMENTS
    void BPLUSTREE_TYPE::MergePage(InternalPage* lpage, InternalPage* rpage) {}

    INDEX_TEMPLATE_ARGUMENTS
    void BPLUSTREE_TYPE::MergePage(LeafPage* lpage, LeafPage* rpage) {}

    /*
    * Insert key & value pair into a page
    */
    INDEX_TEMPLATE_ARGUMENTS
    void BPLUSTREE_TYPE::InsertAt(InternalPage* page, const KeyType& key, page_id_t value) {
        int pos = BinaryFind(page, key);
        MoveRight(page, pos+1);
        page->SetKeyAt(pos+1, key);
        page->SetValueAt(pos+1, value);
    }

    INDEX_TEMPLATE_ARGUMENTS
    bool BPLUSTREE_TYPE::InsertAt(LeafPage* page, const KeyType &key, const ValueType &value) {
        int pos = BinaryFind(page, key);
        if (comparator_(page->KeyAt(pos), key) == 0) {
            return false;
        }
        MoveRight(page, pos+1);
        page->SetKeyAt(pos+1, key);
        page->SetValueAt(pos+1, value);
        return true;
    }


    /*****************************************************************************
     * INDEX ITERATOR
     *****************************************************************************/

    // Find the last pos that is no more than key
    INDEX_TEMPLATE_ARGUMENTS
    auto BPLUSTREE_TYPE::BinaryFind(const LeafPage* leaf_page, const KeyType& key)
        -> int {
        int l = 0;
        int r = leaf_page->GetSize() - 1;
        while (l < r) {
            int mid = (l + r + 1) >> 1;
            if (comparator_(leaf_page->KeyAt(mid), key) != 1) {
                l = mid;
            } else {
                r = mid - 1;
            }
        }

        if (r >= 0 && comparator_(leaf_page->KeyAt(r), key) == 1) {
            r = -1;
        }

        return r;
    }

    // Find the last pos that is no more than key
    INDEX_TEMPLATE_ARGUMENTS
    auto BPLUSTREE_TYPE::BinaryFind(const InternalPage* internal_page,
                                    const KeyType& key) -> int {
        int l = 1;
        int r = internal_page->GetSize() - 1;
        while (l < r) {
            int mid = (l + r + 1) >> 1;
            if (comparator_(internal_page->KeyAt(mid), key) != 1) {
                l = mid;
            } else {
                r = mid - 1;
            }
        }

        if (r == -1 || comparator_(internal_page->KeyAt(r), key) == 1) {
            r = 0;
        }

        return r;
    }

    /*
     * Input parameter is void, find the leftmost leaf page first, then construct
     * index iterator
     * @return : index iterator
     */
    INDEX_TEMPLATE_ARGUMENTS
    auto BPLUSTREE_TYPE::Begin() -> INDEXITERATOR_TYPE
    // Just go left forever
    {
        ReadPageGuard head_guard = bpm_->FetchPageRead(header_page_id_);
        if (head_guard.template As<BPlusTreeHeaderPage>()->root_page_id_ == INVALID_PAGE_ID) {
            return End();
        }
        ReadPageGuard guard = bpm_->FetchPageRead(head_guard.As<BPlusTreeHeaderPage>()->root_page_id_);
        head_guard.Drop();

        auto tmp_page = guard.template As<BPlusTreePage>();
        while (!tmp_page->IsLeafPage()) {
            int slot_num = 0;
            guard = bpm_->FetchPageRead(reinterpret_cast<const InternalPage*>(tmp_page)->ValueAt(slot_num));
            tmp_page = guard.template As<BPlusTreePage>();
        }
        int slot_num = 0;
        if (slot_num != -1) {
            return INDEXITERATOR_TYPE(bpm_, guard.PageId(), 0);
        }
        return End();
    }

    /*
     * Input parameter is low key, find the leaf page that contains the input key
     * first, then construct index iterator
     * @return : index iterator
     */
    INDEX_TEMPLATE_ARGUMENTS
    auto BPLUSTREE_TYPE::Begin(const KeyType& key) -> INDEXITERATOR_TYPE {
        ReadPageGuard head_guard = bpm_->FetchPageRead(header_page_id_);

        if (head_guard.template As<BPlusTreeHeaderPage>()->root_page_id_ == INVALID_PAGE_ID) {
            return End();
        }
        ReadPageGuard guard = bpm_->FetchPageRead(head_guard.As<BPlusTreeHeaderPage>()->root_page_id_);
        head_guard.Drop();
        auto tmp_page = guard.template As<BPlusTreePage>();
        while (!tmp_page->IsLeafPage()) {
            auto internal = reinterpret_cast<const InternalPage*>(tmp_page);
            int slot_num = BinaryFind(internal, key);
            if (slot_num == -1) {
                return End();
            }
            guard = bpm_->FetchPageRead(reinterpret_cast<const InternalPage*>(tmp_page)->ValueAt(slot_num));
            tmp_page = guard.template As<BPlusTreePage>();
        }
        auto* leaf_page = reinterpret_cast<const LeafPage*>(tmp_page);

        int slot_num = BinaryFind(leaf_page, key);
        if (slot_num != -1) {
            return INDEXITERATOR_TYPE(bpm_, guard.PageId(), slot_num);
        }
        return End();
    }

    /*
     * Input parameter is void, construct an index iterator representing the end
     * of the key/value pair in the leaf node
     * @return : index iterator
     */
    INDEX_TEMPLATE_ARGUMENTS
    auto BPLUSTREE_TYPE::End() -> INDEXITERATOR_TYPE {
        return INDEXITERATOR_TYPE(bpm_, -1, -1);
    }

    /**
     * @return Page id of the root of this tree
     */
    INDEX_TEMPLATE_ARGUMENTS
    auto BPLUSTREE_TYPE::GetRootPageId() -> page_id_t {
        ReadPageGuard guard = bpm_->FetchPageRead(header_page_id_);
        auto root_header_page = guard.template As<BPlusTreeHeaderPage>();
        page_id_t root_page_id = root_header_page->root_page_id_;
        return root_page_id;
    }

    /*****************************************************************************
     * UTILITIES AND DEBUG
     *****************************************************************************/

    /*
     * This method is used for test only
     * Read data from file and insert one by one
     */
    INDEX_TEMPLATE_ARGUMENTS
    void BPLUSTREE_TYPE::InsertFromFile(const std::string& file_name,
                                        Transaction* txn) {
        int64_t key;
        std::ifstream input(file_name);
        while (input >> key) {
            KeyType index_key;
            index_key.SetFromInteger(key);
            RID rid(key);
            Insert(index_key, rid, txn);
        }
    }
    /*
     * This method is used for test only
     * Read data from file and remove one by one
     */
    INDEX_TEMPLATE_ARGUMENTS
    void BPLUSTREE_TYPE::RemoveFromFile(const std::string& file_name,
                                        Transaction* txn) {
        int64_t key;
        std::ifstream input(file_name);
        while (input >> key) {
            KeyType index_key;
            index_key.SetFromInteger(key);
            Remove(index_key, txn);
        }
    }

    /*
     * This method is used for test only
     * Read data from file and insert/remove one by one
     */
    INDEX_TEMPLATE_ARGUMENTS
    void BPLUSTREE_TYPE::BatchOpsFromFile(const std::string& file_name,
                                          Transaction* txn) {
        int64_t key;
        char instruction;
        std::ifstream input(file_name);
        while (input) {
            input >> instruction >> key;
            RID rid(key);
            KeyType index_key;
            index_key.SetFromInteger(key);
            switch (instruction) {
            case 'i':
                Insert(index_key, rid, txn);
                break;
            case 'd':
                Remove(index_key, txn);
                break;
            default:
                break;
            }
        }
    }

    INDEX_TEMPLATE_ARGUMENTS
    void BPLUSTREE_TYPE::Print(BufferPoolManager* bpm) {
        auto root_page_id = GetRootPageId();
        auto guard = bpm->FetchPageBasic(root_page_id);
        PrintTree(guard.PageId(), guard.template As<BPlusTreePage>());
    }

    INDEX_TEMPLATE_ARGUMENTS
    void BPLUSTREE_TYPE::PrintTree(page_id_t page_id, const BPlusTreePage* page) {
        if (page->IsLeafPage()) {
            auto* leaf = reinterpret_cast<const LeafPage*>(page);
            std::cout << "Leaf Page: " << page_id << "\tNext: " << leaf->GetNextPageId() << std::endl;

            // Print the contents of the leaf page.
            std::cout << "Contents: ";
            for (int i = 0; i < leaf->GetSize(); i++) {
                std::cout << leaf->KeyAt(i);
                if ((i + 1) < leaf->GetSize()) {
                    std::cout << ", ";
                }
            }
            std::cout << std::endl;
            std::cout << std::endl;
        } else {
            auto* internal = reinterpret_cast<const InternalPage*>(page);
            std::cout << "Internal Page: " << page_id << std::endl;

            // Print the contents of the internal page.
            std::cout << "Contents: ";
            for (int i = 0; i < internal->GetSize(); i++) {
                std::cout << internal->KeyAt(i) << ": " << internal->ValueAt(i);
                if ((i + 1) < internal->GetSize()) {
                    std::cout << ", ";
                }
            }
            std::cout << std::endl;
            std::cout << std::endl;
            for (int i = 0; i < internal->GetSize(); i++) {
                auto guard = bpm_->FetchPageBasic(internal->ValueAt(i));
                PrintTree(guard.PageId(), guard.template As<BPlusTreePage>());
            }
        }
    }

    /**
     * This method is used for debug only, You don't need to modify
     */
    INDEX_TEMPLATE_ARGUMENTS
    void BPLUSTREE_TYPE::Draw(BufferPoolManager* bpm, const std::string& outf) {
        if (IsEmpty()) {
            LOG_WARN("Drawing an empty tree");
            return;
        }

        std::ofstream out(outf);
        out << "digraph G {" << std::endl;
        auto root_page_id = GetRootPageId();
        auto guard = bpm->FetchPageBasic(root_page_id);
        ToGraph(guard.PageId(), guard.template As<BPlusTreePage>(), out);
        out << "}" << std::endl;
        out.close();
    }

    /**
     * This method is used for debug only, You don't need to modify
     */
    INDEX_TEMPLATE_ARGUMENTS
    void BPLUSTREE_TYPE::ToGraph(page_id_t page_id, const BPlusTreePage* page,
                                 std::ofstream& out) {
        std::string leaf_prefix("LEAF_");
        std::string internal_prefix("INT_");
        if (page->IsLeafPage()) {
            auto* leaf = reinterpret_cast<const LeafPage*>(page);
            // Print node name
            out << leaf_prefix << page_id;
            // Print node properties
            out << "[shape=plain color=green ";
            // Print data of the node
            out << "label=<<TABLE BORDER=\"0\" CELLBORDER=\"1\" CELLSPACING=\"0\" "
                   "CELLPADDING=\"4\">\n";
            // Print data
            out << "<TR><TD COLSPAN=\"" << leaf->GetSize() << "\">P=" << page_id
                << "</TD></TR>\n";
            out << "<TR><TD COLSPAN=\"" << leaf->GetSize() << "\">"
                << "max_size=" << leaf->GetMaxSize()
                << ",min_size=" << leaf->GetMinSize() << ",size=" << leaf->GetSize()
                << "</TD></TR>\n";
            out << "<TR>";
            for (int i = 0; i < leaf->GetSize(); i++) {
                out << "<TD>" << leaf->KeyAt(i) << "</TD>\n";
            }
            out << "</TR>";
            // Print table end
            out << "</TABLE>>];\n";
            // Print Leaf node link if there is a next page
            if (leaf->GetNextPageId() != INVALID_PAGE_ID) {
                out << leaf_prefix << page_id << "   ->   " << leaf_prefix
                    << leaf->GetNextPageId() << ";\n";
                out << "{rank=same " << leaf_prefix << page_id << " " << leaf_prefix
                    << leaf->GetNextPageId() << "};\n";
            }
        } else {
            auto* inner = reinterpret_cast<const InternalPage*>(page);
            // Print node name
            out << internal_prefix << page_id;
            // Print node properties
            out << "[shape=plain color=pink ";  // why not?
            // Print data of the node
            out << "label=<<TABLE BORDER=\"0\" CELLBORDER=\"1\" CELLSPACING=\"0\" "
                   "CELLPADDING=\"4\">\n";
            // Print data
            out << "<TR><TD COLSPAN=\"" << inner->GetSize() << "\">P=" << page_id
                << "</TD></TR>\n";
            out << "<TR><TD COLSPAN=\"" << inner->GetSize() << "\">"
                << "max_size=" << inner->GetMaxSize()
                << ",min_size=" << inner->GetMinSize() << ",size=" << inner->GetSize()
                << "</TD></TR>\n";
            out << "<TR>";
            for (int i = 0; i < inner->GetSize(); i++) {
                out << "<TD PORT=\"p" << inner->ValueAt(i) << "\">";
                // if (i > 0) {
                out << inner->KeyAt(i) << "  " << inner->ValueAt(i);
                // } else {
                // out << inner  ->  ValueAt(0);
                // }
                out << "</TD>\n";
            }
            out << "</TR>";
            // Print table end
            out << "</TABLE>>];\n";
            // Print leaves
            for (int i = 0; i < inner->GetSize(); i++) {
                auto child_guard = bpm_->FetchPageBasic(inner->ValueAt(i));
                auto child_page = child_guard.template As<BPlusTreePage>();
                ToGraph(child_guard.PageId(), child_page, out);
                if (i > 0) {
                    auto sibling_guard = bpm_->FetchPageBasic(inner->ValueAt(i - 1));
                    auto sibling_page = sibling_guard.template As<BPlusTreePage>();
                    if (!sibling_page->IsLeafPage() && !child_page->IsLeafPage()) {
                        out << "{rank=same " << internal_prefix << sibling_guard.PageId()
                            << " " << internal_prefix << child_guard.PageId() << "};\n";
                    }
                }
                out << internal_prefix << page_id << ":p" << child_guard.PageId()
                    << "   ->   ";
                if (child_page->IsLeafPage()) {
                    out << leaf_prefix << child_guard.PageId() << ";\n";
                } else {
                    out << internal_prefix << child_guard.PageId() << ";\n";
                }
            }
        }
    }

    INDEX_TEMPLATE_ARGUMENTS
    auto BPLUSTREE_TYPE::DrawBPlusTree() -> std::string {
        if (IsEmpty()) {
            return "()";
        }

        PrintableBPlusTree p_root = ToPrintableBPlusTree(GetRootPageId());
        std::ostringstream out_buf;
        p_root.Print(out_buf);

        return out_buf.str();
    }

    INDEX_TEMPLATE_ARGUMENTS
    auto BPLUSTREE_TYPE::ToPrintableBPlusTree(page_id_t root_id)
        -> PrintableBPlusTree {
        auto root_page_guard = bpm_->FetchPageBasic(root_id);
        auto root_page = root_page_guard.template As<BPlusTreePage>();
        PrintableBPlusTree proot;

        if (root_page->IsLeafPage()) {
            auto leaf_page = root_page_guard.template As<LeafPage>();
            proot.keys_ = leaf_page->ToString();
            proot.size_ = proot.keys_.size() + 4;  // 4 more spaces for indent

            return proot;
        }

        // draw internal page
        auto internal_page = root_page_guard.template As<InternalPage>();
        proot.keys_ = internal_page->ToString();
        proot.size_ = 0;
        for (int i = 0; i < internal_page->GetSize(); i++) {
            page_id_t child_id = internal_page->ValueAt(i);
            PrintableBPlusTree child_node = ToPrintableBPlusTree(child_id);
            proot.size_ += child_node.size_;
            proot.children_.push_back(child_node);
        }

        return proot;
    }

    template class BPlusTree<GenericKey<4>, RID, GenericComparator<4>>;

    template class BPlusTree<GenericKey<8>, RID, GenericComparator<8>>;

    template class BPlusTree<GenericKey<16>, RID, GenericComparator<16>>;

    template class BPlusTree<GenericKey<32>, RID, GenericComparator<32>>;

    template class BPlusTree<GenericKey<64>, RID, GenericComparator<64>>;

}  // namespace bustub